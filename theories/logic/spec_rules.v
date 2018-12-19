(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Rules for updating the specification program. *)
From iris.algebra Require Import auth frac agree gmap list.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Export lang notation.
From reloc.logic Require Export spec_ra.
Import uPred.
Section rules.
  Context `{logrelG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  Local Hint Resolve tpool_lookup.
  Local Hint Resolve tpool_lookup_Some.
  Local Hint Resolve to_tpool_insert.
  Local Hint Resolve to_tpool_insert'.
  Local Hint Resolve tpool_singleton_included.

  (** * Aux. lemmas *)
  Lemma step_insert K tp j e σ κ e' σ' efs :
    tp !! j = Some (fill K e) → head_step e σ κ e' σ' efs →
    erased_step (tp, σ) (<[j:=fill K e']> tp ++ efs, σ').
  Proof.
    intros. rewrite -(take_drop_middle tp j (fill K e)) //.
    rewrite insert_app_r_alt take_length_le ?Nat.sub_diag /=;
      eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(assoc_L (++)) /=. eexists.
    eapply step_atomic; eauto. by apply: Ectx_step'.
  Qed.

  Lemma step_insert_no_fork K tp j e σ κ e' σ' :
    tp !! j = Some (fill K e) → head_step e σ κ e' σ' [] →
    erased_step (tp, σ) (<[j:=fill K e']> tp, σ').
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply step_insert. Qed.

  Lemma nsteps_inv_r {A} n (R : A → A → Prop) x y :
    relations.nsteps R (S n) x y → ∃ z, relations.nsteps R n x z ∧ R z y.
  Proof.
    revert x y; induction n; intros x y.
    - inversion 1; subst.
      match goal with H : relations.nsteps _ 0 _ _ |- _ => inversion H end; subst.
      eexists; repeat econstructor; eauto.
    - inversion 1; subst.
      edestruct IHn as [z [? ?]]; eauto.
      exists z; split; eauto using relations.nsteps_l.
  Qed.

  (** * Main rules *)
  (** Pure reductions *)
  Lemma step_pure E ρ j K e e' (P : Prop) n :
    P →
    PureExec P n e e' →
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K e ={E}=∗ j ⤇ fill K e'.
  Proof.
    iIntros (HP Hex ?) "[#Hspec Hj]".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def /=.
    iInv specN as (tp σ) ">[Hown Hrtc]" "Hclose".
    iDestruct "Hrtc" as %Hrtc.
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[Htpj%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K e'))). }
    iFrame "Hj". iApply "Hclose". iNext. iExists (<[j:=fill K e']> tp), σ.
    rewrite to_tpool_insert'; last eauto.
    iFrame. iPureIntro.
    apply rtc_nsteps in Hrtc; destruct Hrtc as [m Hrtc].
    specialize (Hex HP). apply (nsteps_rtc (m + n)).
    eapply nsteps_trans; eauto.
    revert e e' Htpj Hex.
    induction n => e e' Htpj Hex.
    - inversion Hex; subst.
      rewrite list_insert_id; eauto. econstructor.
    - apply nsteps_inv_r in Hex.
      destruct Hex as [z [Hex1 Hex2]].
      specialize (IHn _ _ Htpj Hex1).
      eapply nsteps_r; eauto.
      replace (<[j:=fill K e']> tp) with
          (<[j:=fill K e']> (<[j:=fill K z]> tp)); last first.
      { clear. revert tp; induction j; intros tp.
        - destruct tp; trivial.
        - destruct tp; simpl; auto. by rewrite IHj. }
      destruct Hex2 as [Hexs Hexd].
      specialize (Hexs σ). destruct Hexs as [e'' [σ' [efs Hexs]]].
      specialize (Hexd σ [] e'' σ' efs Hexs); destruct Hexd as [? [? [? ?]]];
        subst.
      inversion Hexs; simpl in *; subst.
      rewrite -!fill_app.
      eapply step_insert_no_fork; eauto.
      { apply list_lookup_insert. apply lookup_lt_is_Some; eauto. }
  Qed.

  (** Alloc, load, and store *)
  Lemma step_alloc E ρ j K e v :
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (ref e) ={E}=∗ ∃ l, j ⤇ fill K (#l) ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "[#Hinv Hj]".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def /=.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    destruct (exist_fresh (dom (gset loc) (heap σ))) as [l Hl%not_elem_of_dom].
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K (#l)%E))). }
    iMod (own_update with "Hown") as "[Hown Hl]".
    { eapply auth_update_alloc, prod_local_update_2,
        (alloc_singleton_local_update _ l (1%Qp,to_agree v)); last done.
      by apply lookup_to_gen_heap_None. }
    rewrite heapS_mapsto_eq /heapS_mapsto_def /=.
    iExists l. iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (# l)]> tp), (state_upd_heap <[l:=v]> σ).
    rewrite to_gen_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_load E ρ j K l q v:
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ={E}=∗ j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def.
    rewrite heapS_mapsto_eq /heapS_mapsto_def /=.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[? ?%gen_heap_singleton_included]%prod_included ?]%auth_valid_discrete_2.     iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (of_val v)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (of_val v)]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_store E ρ j K l v' e v:
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ={E}=∗ j ⤇ fill K #() ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def.
    rewrite heapS_mapsto_eq /heapS_mapsto_def /=.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included _]%auth_valid_discrete_2.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ Hl%gen_heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K #()))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree v)); last done.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp), (state_upd_heap <[l:=v]> σ).
    rewrite to_gen_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  (** CAS & FAI *)
  Lemma step_cas_fail E ρ j K l q v' e1 v1 e2 v2 :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    nclose specN ⊆ E →
    vals_cas_compare_safe v' v1 →
    v' ≠ v1 →
    spec_ctx ρ ∗ j ⤇ fill K (CAS #l e1 e2) ∗ l ↦ₛ{q} v'
    ={E}=∗ j ⤇ fill K #false ∗ l ↦ₛ{q} v'.
  Proof.
    iIntros (<-<-???) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def heapS_mapsto_eq /heapS_mapsto_def.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ ?%gen_heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (# false)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (#false)]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_cas_suc E ρ j K l e1 v1 v1' e2 v2:
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    nclose specN ⊆ E →
    val_is_unboxed v1 →
    v1 = v1' →
    spec_ctx ρ ∗ j ⤇ fill K (CAS #l e1 e2) ∗ l ↦ₛ v1'
    ={E}=∗ j ⤇ fill K #true ∗ l ↦ₛ v2.
  Proof.
    iIntros (<-<-??<-) "(#Hinv & Hj & Hl)"; subst.
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def heapS_mapsto_eq /heapS_mapsto_def.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included _]%auth_valid_discrete_2.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ Hl%gen_heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (# true)))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree v2)); last done.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (# true)]> tp), (state_upd_heap <[l:=v2]> σ).
    rewrite to_gen_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
    left; eauto.
  Qed.

  Lemma step_fork E ρ j K e :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (Fork e) ={E}=∗ ∃ j', j ⤇ fill K #() ∗ j' ⤇ e.
  Proof.
    iIntros (?) "[#Hspec Hj]".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included ?]%auth_valid_discrete_2.
    assert (j < length tp)%nat by eauto using lookup_lt_Some.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K #()))). }
    iMod (own_update with "Hown") as "[Hown Hfork]".
    { eapply auth_update_alloc, prod_local_update_1,
        (alloc_singleton_local_update _ (length tp) (Excl e)); last done.
      rewrite lookup_insert_ne ?tpool_lookup; last lia.
      by rewrite lookup_ge_None_2. }
    iExists (length tp). iFrame "Hj Hfork". iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp ++ [e]), σ.
    rewrite to_tpool_snoc insert_length to_tpool_insert //. iFrame. iPureIntro.
    eapply rtc_r, step_insert; eauto. econstructor; eauto.
  Qed.

  Lemma step_fai E ρ j K l e1 e2 (i1 i2 : Z) :
    IntoVal e1 #i2 →
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (FAA #l e1) ∗ l ↦ₛ #i1
    ={E}=∗ j ⤇ fill K #i1 ∗ l ↦ₛ #(i1+i2).
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)"; subst.
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def heapS_mapsto_eq /heapS_mapsto_def.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iDestruct (own_valid_2 with "Hown Hj")
      as %[[?%tpool_singleton_included' _]%prod_included _]%auth_valid_discrete_2.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ Hl%gen_heap_singleton_included]%prod_included _]%auth_valid_discrete_2.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (# i1)))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree #(i1+i2))); last done.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (# i1)]> tp), (state_upd_heap <[l:=#(i1+i2)]> σ).
    rewrite to_gen_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. simpl. econstructor; eauto.
  Qed.

End rules.
