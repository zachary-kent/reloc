(* ReLoC -- Relational logic for fine-grained concurrency *)
(** The definition of the refinement proposition.
    - The model for types and type combinators;
    - Closure under context substitutions;
    - Basic monadic rules *)
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import list.
From iris.heap_lang Require Import notation proofmode.
From reloc Require Import logic.spec_rules prelude.ctx_subst.

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
  Context `{relocG Σ}.

  Instance lty2_equiv : Equiv lty2 := λ A B, ∀ w1 w2, A w1 w2 ≡ B w1 w2.
  Instance lty2_dist : Dist lty2 := λ n A B, ∀ w1 w2, A w1 w2 ≡{n}≡ B w1 w2.
  Lemma lty2_ofe_mixin : OfeMixin lty2.
  Proof. by apply (iso_ofe_mixin (lty2_car : lty2 → (val -c> val -c> iProp Σ))). Qed.
  Canonical Structure lty2C := OfeT lty2 lty2_ofe_mixin.
  Global Instance lty2_cofe : Cofe ltyC2.
  Proof.
    (* apply (iso_cofe_subtype' (λ A : val -c> val -c> iProp Σ, ∀ w1 w2, Persistent (A w1 w2)) *)
    (*   (@Lty2 _ _ _) lty2_car)=> //. *)
    (* - apply _. *)
    (* - apply limit_preserving_forall=> w. *)
    (*   by apply bi.limit_preserving_Persistent=> n ??. *)
  Admitted.

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
    Proper ((=) ==> (=) ==> (=) ==> dist n) (interp_expr E).
  Proof. solve_proper. Qed.

  Definition lty2_unit : lty2 := Lty2 (λ w1 w2, ⌜ w1 = #() ∧ w2 = #() ⌝%I).
  Definition lty2_bool : lty2 := Lty2 (λ w1 w2, ∃ b : bool, ⌜ w1 = #b ∧ w2 = #b ⌝)%I.
  Definition lty2_int : lty2 := Lty2 (λ w1 w2, ∃ n : Z, ⌜ w1 = #n ∧ w2 = #n ⌝)%I.

  Definition lty2_arr (A1 A2 : lty2) : lty2 := Lty2 (λ w1 w2,
    □ ∀ v1 v2, A1 v1 v2 -∗ interp_expr ⊤ (App w1 v1) (App w2 v2) A2)%I.

  Definition lty2_ref (A : lty2) : lty2 := Lty2 (λ w1 w2,
    ∃ l1 l2: loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (relocN .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ₛ v2 ∗ A v1 v2))%I.

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
    iInv (relocN.@(l, l1')) as (? ?) "[>Hl ?]" "Hcl".
    iInv (relocN.@(l, l2')) as (? ?) "[>Hl' ?]" "Hcl'".
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
    iInv (relocN.@(l1', l)) as (? ?) "(? & >Hl & ?)" "Hcl".
    iInv (relocN.@(l2', l)) as (? ?) "(? & >Hl' & ?)" "Hcl'".
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

End environment_properties.

Notation "'{' E ';' Γ '}' ⊨ e1 '<<' e2 : A" :=
  (refines E Γ e1%E e2%E (A)%lty2)
  (at level 100, E at level 50, Γ at next level, e1, e2 at next level,
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

Section monadic.
  Context `{relocG Σ}.

  Lemma refines_ret E Γ e1 e2 A :
    is_closed_expr [] e1 →
    is_closed_expr [] e2 →
    interp_expr E e1 e2 A -∗ {E;Γ} ⊨ e1 << e2 : A.
  Proof.
    iIntros (??) "HA".
    rewrite refines_eq /refines_def.
    iIntros (vvs ρ) "#Hs #HΓ".
    rewrite !subst_map_is_closed_nil//.
  Qed.

  Lemma refines_bind A E Γ A' e e' K K' :
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

End monadic.

Typeclasses Opaque env_ltyped2.