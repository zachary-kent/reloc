(* ReLoC -- Relational logic for fine-grained concurrency *)
(** The definition of the refinement proposition.
    - The model for types and type combinators;
    - Closure under context substitutions;
    - Basic monadic rules *)
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import list gmap.
From iris.heap_lang Require Import notation proofmode.
From reloc Require Import logic.spec_rules prelude.ctx_subst.
From reloc Require Export logic.spec_ra.

(** Semantic intepretation of types *)
Record lty2 `{invG Σ} := Lty2 {
  lty2_car :> val → val → iProp Σ;
  lty2_persistent v1 v2 : Persistent (lty2_car v1 v2)
}.
Arguments Lty2 {_ _} _%I {_}.
Arguments lty2_car {_ _} _ _ _ : simpl never.
Bind Scope lty_scope with lty2.
Delimit Scope lty_scope with lty2.
Existing Instance lty2_persistent.

(* The COFE structure on semantic types *)
Section lty2_ofe.
  Context `{invG Σ}.

  Instance lty2_equiv : Equiv lty2 := λ A B, ∀ w1 w2, A w1 w2 ≡ B w1 w2.
  Instance lty2_dist : Dist lty2 := λ n A B, ∀ w1 w2, A w1 w2 ≡{n}≡ B w1 w2.
  Lemma lty2_ofe_mixin : OfeMixin lty2.
  Proof. by apply (iso_ofe_mixin (lty2_car : lty2 → (val -c> val -c> iProp Σ))). Qed.
  Canonical Structure lty2C := OfeT lty2 lty2_ofe_mixin.

  Global Instance lty2_cofe : Cofe lty2C.
  Proof.
    apply (iso_cofe_subtype' (λ A : val -c> val -c> iProp Σ, ∀ w1 w2, Persistent (A w1 w2)) (@Lty2 _ _) lty2_car)=>//.
    - apply _.
    - apply limit_preserving_forall=> w1.
      apply limit_preserving_forall=> w2.
      apply bi.limit_preserving_Persistent.
      intros n P Q HPQ. apply (HPQ w1 w2).
  Qed.

  Global Instance lty2_inhabited : Inhabited lty2 := populate (Lty2 inhabitant).

  Global Instance lty2_car_ne n : Proper (dist n ==> (=) ==> (=) ==> dist n) lty2_car.
  Proof. by intros A A' ? w1 w2 <- ? ? <-. Qed.
  Global Instance lty2_car_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) lty2_car.
  Proof. by intros A A' ? w1 w2 <- ? ? <-. Qed.
End lty2_ofe.

Section semtypes.
  Context `{relocG Σ}.

  Implicit Types A B : lty2.

  Definition interp_expr (E : coPset) (e e' : expr)
             (A : lty2) : iProp Σ :=
    (∀ j K, j ⤇ fill K e'
    ={E,⊤}=∗ WP e {{ v, ∃ v', j ⤇ fill K (of_val v') ∗ A v v' }})%I.

  Global Instance interp_expr_ne E n :
    Proper ((=) ==> (=) ==> dist n ==> dist n) (interp_expr E).
  Proof. solve_proper. Qed.

  Global Instance interp_expr_proper E e e' :
    Proper ((≡) ==> (≡)) (interp_expr E e e').
  Proof. apply ne_proper=>n. by apply interp_expr_ne. Qed.

  Definition lty2_unit : lty2 := Lty2 (λ w1 w2, ⌜ w1 = #() ∧ w2 = #() ⌝%I).
  Definition lty2_bool : lty2 := Lty2 (λ w1 w2, ∃ b : bool, ⌜ w1 = #b ∧ w2 = #b ⌝)%I.
  Definition lty2_int : lty2 := Lty2 (λ w1 w2, ∃ n : Z, ⌜ w1 = #n ∧ w2 = #n ⌝)%I.

  Definition lty2_arr (A1 A2 : lty2) : lty2 := Lty2 (λ w1 w2,
    □ ∀ v1 v2, A1 v1 v2 -∗ interp_expr ⊤ (App w1 v1) (App w2 v2) A2)%I.

  Definition lty2_ref (A : lty2) : lty2 := Lty2 (λ w1 w2,
    ∃ l1 l2: loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (relocN .@ "ref" .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ₛ v2 ∗ A v1 v2))%I.

  Definition lty2_prod (A B : lty2) : lty2 := Lty2 (λ w1 w2,
    ∃ v1 v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧
        A v1 v2 ∗ B v1' v2')%I.

  Definition lty2_sum (A B : lty2) : lty2 := Lty2 (λ w1 w2,
    ∃ v1 v2, (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ A v1 v2)
          ∨  (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ B v1 v2))%I.

  Definition lty2_rec1 (C : lty2C -n> lty2C) (rec : lty2) : lty2 :=
    Lty2 (λ w1 w2, ▷ C rec w1 w2)%I.
  Instance lty2_rec1_contractive C : Contractive (lty2_rec1 C).
  Proof.
    intros n. intros P Q HPQ.
    unfold lty2_rec1. intros w1 w2.
    apply bi.later_contractive.
    destruct n; try done.
    simpl in HPQ; simpl. f_equiv. by apply C.
  Qed.

  Definition lty2_rec (C : lty2C -n> lty2C) : lty2 := fixpoint (lty2_rec1 C).

  Definition lty2_exists (C : lty2 → lty2) : lty2 := Lty2 (λ w1 w2,
    ∃ A : lty2, C A w1 w2)%I.

  (** The lty2 constructors are non-expansive *)
  Instance lty2_prod_ne n : Proper (dist n ==> (dist n ==> dist n)) lty2_prod.
  Proof. solve_proper. Qed.

  Instance lty2_sum_ne n : Proper (dist n ==> (dist n ==> dist n)) lty2_sum.
  Proof. solve_proper. Qed.

  Instance lty2_arr_ne n : Proper (dist n ==> dist n ==> dist n) lty2_arr.
  Proof. solve_proper. Qed.

  Instance lty2_rec_ne n : Proper (dist n ==> dist n)
                                   (lty2_rec : (lty2C -n> lty2C) -> lty2C).
  Proof.
    intros F F' HF.
    unfold lty2_rec, lty2_car.
    apply fixpoint_ne=> X w1 w2.
    unfold lty2_rec1, lty2_car. cbn.
    f_equiv.
    apply lty2_car_ne; eauto.
  Qed.

  Lemma lty_rec_unfold (C : lty2C -n> lty2C) : lty2_rec C ≡ lty2_rec1 C (lty2_rec C).
  Proof. apply fixpoint_unfold. Qed.

End semtypes.

(* Nice notations *)
Notation "()" := lty2_unit : lty_scope.
Infix "→" := lty2_arr : lty_scope.
Notation "'ref' A" := (lty2_ref A) : lty_scope.

(* The semantic typing judgment *)
Definition env_ltyped2 `{relocG Σ} (Γ : gmap string lty2)
    (vs : gmap string (val*val)) : iProp Σ :=
  (⌜ ∀ x, is_Some (Γ !! x) ↔ is_Some (vs !! x) ⌝ ∧
  [∗ map] i ↦ Avv ∈ map_zip Γ vs, lty2_car Avv.1 Avv.2.1 Avv.2.2)%I.

Instance env_ltyped2_ne `{relocG Σ} n :
  Proper (dist n ==> (=) ==> dist n) env_ltyped2.
Proof.
  intros Γ Γ' HΓ ? vvs ->.
  rewrite /env_ltyped2.
  f_equiv.
  - repeat f_equiv. split.
    { intros Hvvs x. split; intros HH.
      - apply Hvvs. destruct (Γ !! x) as [?|] eqn:lawl; eauto.
        specialize (HΓ x). revert HΓ.
        destruct HH as [? HH].
        rewrite HH lawl. inversion 1.
      - destruct (Γ' !! x) as [?|] eqn:lawl; eauto.
        specialize (HΓ x). revert HΓ.
        apply (Hvvs x) in HH.
        destruct HH as [? HH].
        rewrite HH lawl. inversion 1. }
    (* MM TASTY COPYPASTA WITH CARBONARYA SAUCE *)
    { intros Hvvs x. split; intros HH.
      - apply Hvvs. destruct (Γ' !! x) as [?|] eqn:lawl; eauto.
        specialize (HΓ x). revert HΓ.
        destruct HH as [? HH].
        rewrite HH lawl. inversion 1.
      - destruct (Γ !! x) as [?|] eqn:lawl; eauto.
        specialize (HΓ x). revert HΓ.
        apply (Hvvs x) in HH.
        destruct HH as [? HH].
        rewrite HH lawl. inversion 1. }
  - admit.
Admitted.

(* Hmmm *)
Instance env_ltyped2_proper `{relocG Σ} :
  Proper ((≡) ==> (=) ==> (≡)) env_ltyped2.
Proof.
  intros Γ Γ' HΓ ? vvs ->.
  apply equiv_dist=>n.
  setoid_rewrite equiv_dist in HΓ.
  by rewrite HΓ.
Qed.

Section refinement.
  Context `{relocG Σ}.

  Definition refines_def  (E : coPset)
           (Γ : gmap string lty2)
           (e e' : expr) (A : lty2) : iProp Σ :=
    (∀ vvs ρ, spec_ctx ρ -∗
              env_ltyped2 Γ vvs -∗
              interp_expr E (subst_map (fst <$> vvs) e)
                            (subst_map (snd <$> vvs) e')
                            A)%I.
  Definition refines_aux : seal refines_def. Proof. by eexists. Qed.
  Definition refines := unseal refines_aux.
  Definition refines_eq : refines = refines_def :=
    seal_eq refines_aux.

  Global Instance refines_ne E n :
    Proper ((dist n) ==> (=) ==> (=) ==> (dist n) ==> (dist n)) (refines E).
  Proof.
    rewrite refines_eq /refines_def.
    solve_proper.
  Qed.

  (* TODO: this is a bit icky *)
  Global Instance refines_proper E  :
    Proper ((≡) ==> (=) ==> (=) ==> (≡) ==> (≡)) (refines E).
  Proof.
    intros Γ Γ' HΓ ? e -> ? e' -> A A' HA.
    apply equiv_dist=>n.
    setoid_rewrite equiv_dist in HA.
    setoid_rewrite equiv_dist in HΓ.
    by rewrite HA HΓ.
  Defined.

End refinement.

Notation "⟦ A ⟧ₑ" := (λ e e', interp_expr ⊤ e e' A).
Notation "⟦ Γ ⟧*" := (env_ltyped2 Γ).

Section semtypes_properties.
  Context `{relocG Σ}.

  (* The reference type relation is functional and injective.
     Thanks to Amin. *)
  Lemma interp_ref_funct E (A : lty2) (l l1 l2 : loc) :
    ↑relocN ⊆ E →
    (ref A)%lty2 #l #l1 ∗ (ref A)%lty2 #l #l2
    ={E}=∗ ⌜l1 = l2⌝.
  Proof.
    iIntros (?) "[Hl1 Hl2] /=".
    iDestruct "Hl1" as (l' l1') "[% [% #Hl1]]". simplify_eq.
    iDestruct "Hl2" as (l l2') "[% [% #Hl2]]". simplify_eq.
    destruct (decide (l1' = l2')) as [->|?]; eauto.
    iInv (relocN.@"ref".@(l, l1')) as (? ?) "[>Hl ?]" "Hcl".
    iInv (relocN.@"ref".@(l, l2')) as (? ?) "[>Hl' ?]" "Hcl'".
    simpl. iExFalso.
    iDestruct (gen_heap.mapsto_valid_2 with "Hl Hl'") as %Hfoo.
    compute in Hfoo. eauto.
  Qed.

  Lemma interp_ref_inj E (A : lty2) (l l1 l2 : loc) :
    ↑relocN ⊆ E →
    (ref A)%lty2 #l1 #l ∗ (ref A)%lty2 #l2 #l
    ={E}=∗ ⌜l1 = l2⌝.
  Proof.
    iIntros (?) "[Hl1 Hl2] /=".
    iDestruct "Hl1" as (l1' l') "[% [% #Hl1]]". simplify_eq.
    iDestruct "Hl2" as (l2' l) "[% [% #Hl2]]". simplify_eq.
    destruct (decide (l1' = l2')) as [->|?]; eauto.
    iInv (relocN.@"ref".@(l1', l)) as (? ?) "(? & >Hl & ?)" "Hcl".
    iInv (relocN.@"ref".@(l2', l)) as (? ?) "(? & >Hl' & ?)" "Hcl'".
    simpl. iExFalso.
    iDestruct (mapsto_valid_2 with "Hl Hl'") as %Hfoo.
    compute in Hfoo. eauto.
  Qed.

  Lemma interp_ret (A : lty2) E e1 e2 v1 v2 :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    (|={E,⊤}=> A v1 v2)%I -∗ interp_expr E e1 e2 A.
  Proof.
    iIntros (<- <-) "HA".
    iIntros (j K) "Hj /=". iMod "HA".
    iApply wp_value; eauto.
  Qed.
End semtypes_properties.

Section environment_properties.
  Context `{relocG Σ}.
  Implicit Types A B : lty2.
  Implicit Types Γ : gmap string lty2.

  Lemma env_ltyped2_lookup Γ vs x A :
    Γ !! x = Some A →
    ⟦ Γ ⟧* vs -∗ ∃ v1 v2, ⌜ vs !! x = Some (v1,v2) ⌝ ∧ A v1 v2.
  Proof.
    iIntros (HΓx) "[Hlookup HΓ]". iDestruct "Hlookup" as %Hlookup.
    destruct (proj1 (Hlookup x)) as [v Hx]; eauto.
    iExists v.1,v.2. iSplit; first by destruct v.
    iApply (big_sepM_lookup _ _ x (A,v) with "HΓ").
    by rewrite map_lookup_zip_with HΓx /= Hx.
  Qed.

  Lemma env_ltyped2_insert Γ vs x A v1 v2 :
    A v1 v2 -∗ ⟦ Γ ⟧* vs -∗
    ⟦ (binder_insert x A Γ) ⟧* (binder_insert x (v1,v2) vs).
  Proof.
    destruct x as [|x]=> /=; first by auto.
    iIntros "#HA [Hlookup #HΓ]". iDestruct "Hlookup" as %Hlookup. iSplit.
    - iPureIntro=> y. rewrite !lookup_insert_is_Some'. naive_solver.
    - rewrite -map_insert_zip_with. by iApply big_sepM_insert_2.
  Qed.

  Lemma env_ltyped2_empty :
    ⟦ ∅ ⟧* ∅.
  Proof.
    iSplit.
    - iPureIntro=> y. rewrite !lookup_empty -!not_eq_None_Some. by naive_solver.
    - by rewrite map_zip_with_empty.
  Qed.

  Global Instance env_ltyped2_persistent Γ vs : Persistent (⟦ Γ ⟧* vs).
  Proof. apply _. Qed.

End environment_properties.

Notation "'{' E ';' Γ '}' ⊨ e1 '<<' e2 : A" :=
  (refines E Γ e1%E e2%E (A)%lty2)
  (at level 100, E at next level, Γ at next level, e1, e2 at next level,
   A at level 200,
   format "'[hv' '{' E ';' Γ '}'  ⊨  '/  ' e1  '/' '<<'  '/  ' e2  :  A ']'").
Notation "Γ ⊨ e1 '<<' e2 : A" :=
  (refines ⊤ Γ e1%E e2%E (A)%lty2)%I
  (at level 100, e1, e2 at next level,
   A at level 200,
   format "'[hv' Γ  ⊨  '/  ' e1  '/' '<<'  '/  ' e2  :  A ']'").

(** Properties of the relational interpretation *)
Section related_facts.
  Context `{relocG Σ}.

  (* We need this to be able to open and closed invariants in front of logrels *)
  Lemma fupd_logrel E1 E2 Γ e e' A :
    ((|={E1,E2}=> {E2;Γ} ⊨ e << e' : A)
     -∗ ({E1;Γ} ⊨ e << e' : A))%I.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "H".
    iIntros (vvs ρ) "#Hs HΓ"; iIntros (j K) "Hj /=".
    iMod "H" as "H".
    iApply ("H" with "Hs HΓ Hj").
  Qed.

  Global Instance elim_fupd_logrel p E1 E2 Γ e e' P A :
   (* TODO: DF: look at the booleans here *)
   ElimModal True p false (|={E1,E2}=> P) P
     ({E1;Γ} ⊨ e << e' : A) ({E2;Γ} ⊨ e << e' : A).
  Proof.
    rewrite /ElimModal. intros _.
    iIntros "[HP HI]". iApply fupd_logrel.
    destruct p; simpl; rewrite ?bi.intuitionistically_elim;
    iMod "HP"; iModIntro; by iApply "HI".
  Qed.

  Global Instance elim_bupd_logrel p E Γ e e' P A :
   ElimModal True p false (|==> P) P
     ({E;Γ} ⊨ e << e' : A) ({E;Γ} ⊨ e << e' : A).
  Proof.
    rewrite /ElimModal (bupd_fupd E).
    apply: elim_fupd_logrel.
  Qed.

  (* This + elim_modal_timless_bupd' is useful for stripping off laters of timeless propositions. *)
  Global Instance is_except_0_logrel E Γ e e' A :
    IsExcept0 ({E;Γ} ⊨ e << e' : A).
  Proof.
    rewrite /IsExcept0.
    iIntros "HL".
    iApply fupd_logrel.
    by iMod "HL".
  Qed.

End related_facts.

(** TODO this is a terrible hack and I should be ashamed of myself.
    See iris issue 225. *)
Notation is_closed_expr' := (λ e, ∀ vs, subst_map vs e = e).

Section monadic.
  Context `{relocG Σ}.

  Lemma refines_ret' E Γ e1 e2 A :
    is_closed_expr' e1 →
    is_closed_expr' e2 →
    interp_expr E e1 e2 A -∗ {E;Γ} ⊨ e1 << e2 : A.
  Proof.
    iIntros (Hcl1 Hcl2) "HA".
    rewrite refines_eq /refines_def.
    iIntros (vvs ρ) "#Hs #HΓ".
    by rewrite Hcl1 Hcl2.
  Qed.

  Lemma refines_bind K K' E Γ A A' e e' :
    ({E;Γ} ⊨ e << e' : A) -∗
    (∀ v v', A v v' -∗
             ({⊤;Γ} ⊨ fill K (of_val v) << fill K' (of_val v') : A')) -∗
    ({E;Γ} ⊨ fill K e << fill K' e' : A').
  Proof.
    iIntros "Hm Hf".
    rewrite refines_eq /refines_def.
    iIntros (vvs ρ) "#Hs #HΓ". iSpecialize ("Hm" with "Hs HΓ").
    iIntros (j K₁) "Hj /=".
    rewrite !subst_map_fill -fill_app.
    iMod ("Hm" with "Hj") as "Hm".
    iModIntro. iApply wp_bind.
    iApply (wp_wand with "Hm").
    iIntros (v). iDestruct 1 as (v') "[Hj HA]".
    change (of_val v')
      with (subst_map (snd <$> vvs) (of_val v')).
    rewrite fill_app -!subst_map_fill.
    iMod ("Hf" with "HA Hs HΓ Hj") as "Hf/=".
    by rewrite !subst_map_fill /=.
  Qed.

  Lemma refines_ret E Γ e1 e2 v1 v2 (A : lty2) :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    (|={E,⊤}=> A v1 v2) -∗ {E;Γ} ⊨ e1 << e2 : A.
  Proof.
    iIntros (<-<-) "HA".
    rewrite refines_eq /refines_def.
    iIntros (vvs ρ) "#Hs #HΓ". simpl.
    iIntros (j K) "Hj /=".
    iMod "HA" as "HA". iModIntro.
    iApply wp_value. iExists _. by iFrame.
  Qed.

End monadic.

Typeclasses Opaque env_ltyped2.
