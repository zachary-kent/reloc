(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Rules for updating the specification program. *)
From iris.algebra Require Import auth excl frac agree gmap list.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Export lang notation tactics.
From reloc.logic Require Export spec_ra.
Import uPred.

Section rules.
  Context `{relocG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  Local Hint Resolve tpool_lookup : core.
  Local Hint Resolve tpool_lookup_Some : core.
  Local Hint Resolve to_tpool_insert : core.
  Local Hint Resolve to_tpool_insert' : core.
  Local Hint Resolve tpool_singleton_included : core.

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

  (** * Main rules *)
  (** Pure reductions *)
  Lemma step_pure E j K e e' (P : Prop) n :
    P →
    PureExec P n e e' →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K e ={E}=∗ spec_ctx ∗ j ⤇ fill K e'.
  Proof.
    iIntros (HP Hex ?) "[#Hspec Hj]". iFrame "Hspec".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def /=.
    iDestruct "Hspec" as (ρ) "Hspec".
    iInv specN as (tp σ) ">[Hown Hrtc]" "Hclose".
    iDestruct "Hrtc" as %Hrtc.
    iCombine "Hown Hj"
      gives %[[Htpj%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { eapply auth_update, prod_local_update_1.
      by eapply (singleton_local_update _ j (Excl (fill K e))),
        (exclusive_local_update _ (Excl (fill K e'))). }
    iFrame "Hj". iApply "Hclose". iNext. iExists (<[j:=fill K e']> tp), σ.
    rewrite to_tpool_insert'; last eauto.
    iFrame. iPureIntro.
    apply rtc_nsteps_1 in Hrtc; destruct Hrtc as [m Hrtc].
    specialize (Hex HP). apply (rtc_nsteps_2 (m + n)).
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

  (** Prophecy variables (at this point those are just noops) *)
  Lemma step_newproph E j K :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K NewProph ={E}=∗
    ∃ (p : proph_id), spec_ctx ∗ j ⤇ fill K #p.
  Proof.
    iIntros (?) "[#Hinv Hj]". iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def /=.
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid_discrete.
    destruct (exist_fresh (used_proph_id σ)) as [p Hp].
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
         singleton_local_update, (exclusive_local_update _ (Excl (fill K #p))). }
    iExists p. iFrame. iApply "Hclose". iNext.
    iExists (<[j:=fill K #p]> tp), (state_upd_used_proph_id ({[ p ]} ∪.) σ).
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_resolveproph E j K (p : proph_id) w :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (ResolveProph #p (of_val w)) ={E}=∗
    spec_ctx ∗ j ⤇ fill K #().
  Proof.
    iIntros (?) "[#Hinv Hj]". iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def /=.
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
         singleton_local_update, (exclusive_local_update _ (Excl (fill K #()))). }
    iFrame. iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. do 2 econstructor; eauto.
  Qed.

  (** Alloc, load, and store *)
  Lemma step_alloc E j K e v :
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (ref e) ={E}=∗ ∃ l, spec_ctx ∗ j ⤇ fill K (#l) ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "[#Hinv Hj]". iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def /=.
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    destruct (exist_fresh (dom (heap σ))) as [l Hl%not_elem_of_dom].
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update, (exclusive_local_update _ (Excl (fill K (#l)%E))). }
    iMod (own_update with "Hown") as "[Hown Hl]".
    { eapply auth_update_alloc, prod_local_update_2,
        (alloc_singleton_local_update _ l (1%Qp,to_agree (Some v : leibnizO _))); last done.
      by apply lookup_to_heap_None. }
    rewrite heapS_mapsto_eq /heapS_mapsto_def /=.
    iExists l. iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (# l)]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    rewrite -state_init_heap_singleton. eapply AllocNS; first by lia.
    intros. assert (i = 0) as -> by lia. by rewrite Loc.add_0.
  Qed.

  Lemma step_load E j K l q v:
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (!#l) ∗ l ↦ₛ{q} v
    ={E}=∗ spec_ctx ∗ j ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def.
    iDestruct "Hinv" as (ρ) "Hinv".
    rewrite heapS_mapsto_eq /heapS_mapsto_def /=.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete.
    iCombine "Hown Hl"
      gives %[[? ?%heap_singleton_included]%prod_included ?]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (of_val v)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (of_val v)]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_store E j K l v' e v:
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (#l <- e) ∗ l ↦ₛ v'
    ={E}=∗ spec_ctx ∗ j ⤇ fill K #() ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def.
    iDestruct "Hinv" as (ρ) "Hinv".
    rewrite heapS_mapsto_eq /heapS_mapsto_def /=.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid_discrete.
    iCombine "Hown Hl"
      gives %[[_ Hl%heap_singleton_included]%prod_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K #()))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2.
      apply: singleton_local_update.
      { by rewrite /to_heap lookup_fmap Hl. }
      apply: (exclusive_local_update _
        (1%Qp, to_agree (Some v : leibnizO (option val)))).
      apply: pair_exclusive_l. done. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K #()]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_xchg E j K l e (v v' : val) :
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Xchg #l e) ∗ l ↦ₛ v'
    ={E}=∗ spec_ctx ∗ j ⤇ fill K (of_val v') ∗ l ↦ₛ v.
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def.
    iDestruct "Hinv" as (ρ) "Hinv".
    rewrite heapS_mapsto_eq /heapS_mapsto_def /=.
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid_discrete.
    iCombine "Hown Hl"
      gives %[[_ Hl%heap_singleton_included]%prod_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (of_val v')))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2.
      apply: singleton_local_update.
      { by rewrite /to_heap lookup_fmap Hl. }
      apply: (exclusive_local_update _
        (1%Qp, to_agree (Some v : leibnizO (option val)))).
      apply: pair_exclusive_l. done. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (of_val v')]> tp), (state_upd_heap <[l:=Some v]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  (** CmpXchg & FAA *)
  Lemma step_cmpxchg_fail E j K l q v' e1 v1 e2 v2 :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    nclose specN ⊆ E →
    vals_compare_safe v' v1 →
    v' ≠ v1 →
    spec_ctx ∗ j ⤇ fill K (CmpXchg #l e1 e2) ∗ l ↦ₛ{q} v'
    ={E}=∗ spec_ctx ∗ j ⤇ fill K (v', #false)%V ∗ l ↦ₛ{q} v'.
  Proof.
    iIntros (<-<-???) "(#Hinv & Hj & Hl)". iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def heapS_mapsto_eq /heapS_mapsto_def.
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete.
    iCombine "Hown Hl"
      gives %[[_ ?%heap_singleton_included]%prod_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (_, #false)%V))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (_, #false)%V]> tp), σ.
    rewrite to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
    rewrite bool_decide_false //.
  Qed.

  Lemma step_cmpxchg_suc E j K l e1 v1 v1' e2 v2:
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    nclose specN ⊆ E →
    vals_compare_safe v1' v1 →
    v1' = v1 →
    spec_ctx ∗ j ⤇ fill K (CmpXchg #l e1 e2) ∗ l ↦ₛ v1'
    ={E}=∗ spec_ctx ∗ j ⤇ fill K (v1', #true)%V ∗ l ↦ₛ v2.
  Proof.
    iIntros (<-<-???) "(#Hinv & Hj & Hl)"; subst. iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def heapS_mapsto_eq /heapS_mapsto_def.
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid_discrete.
    iCombine "Hown Hl"
      gives %[[_ Hl%heap_singleton_included]%prod_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (_, #true)%V))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2.
      apply: singleton_local_update.
      { by rewrite /to_heap lookup_fmap Hl. }
      apply: (exclusive_local_update _
        (1%Qp, to_agree (Some v2 : leibnizO (option val)))).
      apply: pair_exclusive_l. done. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (_, #true)%V]> tp), (state_upd_heap <[l:=Some v2]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
    rewrite bool_decide_true //.
  Qed.

  Lemma step_faa E j K l e1 e2 (i1 i2 : Z) :
    IntoVal e1 #i2 →
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (FAA #l e1) ∗ l ↦ₛ #i1
    ={E}=∗ spec_ctx ∗ j ⤇ fill K #i1 ∗ l ↦ₛ #(i1+i2).
  Proof.
    iIntros (<-?) "(#Hinv & Hj & Hl)"; subst. iFrame "Hinv".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def heapS_mapsto_eq /heapS_mapsto_def.
    iDestruct "Hinv" as (ρ) "Hinv".
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included _]%auth_both_valid_discrete.
    iCombine "Hown Hl"
      gives %[[_ Hl%heap_singleton_included]%prod_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (# i1)))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2.
      apply: singleton_local_update.
      { by rewrite /to_heap lookup_fmap Hl. }
      apply: (exclusive_local_update _
        (1%Qp, to_agree (Some #(i1+i2) : leibnizO (option val)))).
      apply: pair_exclusive_l. done. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (<[j:=fill K (# i1)]> tp), (state_upd_heap <[l:=Some #(i1+i2)]> σ).
    rewrite to_heap_insert to_tpool_insert'; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. simpl. econstructor; eauto.
  Qed.

  (** Fork *)
  Lemma step_fork E j K e :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (Fork e) ={E}=∗
    ∃ j', (spec_ctx ∗ j ⤇ fill K #()) ∗ (spec_ctx ∗ j' ⤇ e).
  Proof.
    iIntros (?) "[#Hspec Hj]". iFrame "Hspec".
    rewrite /spec_ctx tpool_mapsto_eq /tpool_mapsto_def.
    iDestruct "Hspec" as (ρ) "Hspec".
    iInv specN as (tp σ) ">[Hown %]" "Hclose".
    iCombine "Hown Hj"
      gives %[[?%tpool_singleton_included' _]%prod_included ?]%auth_both_valid_discrete.
    assert (j < length tp) by eauto using lookup_lt_Some.
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

End rules.
