(* ReLoC -- Relational logic for fine-grained concurrency *)
(** The definition of the refinement proposition.
    - The model for types and type combinators;
    - Closure under context substitutions;
    - Basic monadic rules *)
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import list gmap.
From iris.heap_lang Require Export lang notation.
From iris.heap_lang Require Import proofmode.
From reloc Require Import prelude.properness logic.spec_rules prelude.ctx_subst.
From reloc Require Export logic.spec_ra.

(** Semantic intepretation of types *)
Record lty2 Σ := Lty2 {
  lty2_car :> val → val → iProp Σ;
  lty2_persistent v1 v2 : Persistent (lty2_car v1 v2)
}.
Arguments Lty2 {_} _%I {_}.
Arguments lty2_car {_} _ _ _ : simpl never.
Bind Scope lty_scope with lty2.
Delimit Scope lty_scope with lty2.
Existing Instance lty2_persistent.

(* The COFE structure on semantic types *)
Section lty2_ofe.
  Context `{Σ : gFunctors}.

  Instance lty2_equiv : Equiv (lty2 Σ) := λ A B, ∀ w1 w2, A w1 w2 ≡ B w1 w2.
  Instance lty2_dist : Dist (lty2 Σ) := λ n A B, ∀ w1 w2, A w1 w2 ≡{n}≡ B w1 w2.
  Lemma lty2_ofe_mixin : OfeMixin (lty2 Σ).
  Proof. by apply (iso_ofe_mixin (lty2_car : lty2 Σ → (val -c> val -c> iProp Σ))). Qed.
  Canonical Structure lty2C := OfeT (lty2 Σ) lty2_ofe_mixin.

  Global Instance lty2_cofe : Cofe lty2C.
  Proof.
    apply (iso_cofe_subtype' (λ A : val -c> val -c> iProp Σ, ∀ w1 w2, Persistent (A w1 w2)) (@Lty2 _) lty2_car)=>//.
    - apply _.
    - apply limit_preserving_forall=> w1.
      apply limit_preserving_forall=> w2.
      apply bi.limit_preserving_Persistent.
      intros n P Q HPQ. apply (HPQ w1 w2).
  Qed.

  Global Instance lty2_inhabited : Inhabited (lty2 Σ) := populate (Lty2 inhabitant).

  Global Instance lty2_car_ne n : Proper (dist n ==> (=) ==> (=) ==> dist n) lty2_car.
  Proof. by intros A A' ? w1 w2 <- ? ? <-. Qed.
  Global Instance lty2_car_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) lty2_car.
  Proof. solve_proper_from_ne. Qed.
End lty2_ofe.

Arguments lty2C : clear implicits.

Section semtypes.
  Context `{relocG Σ}.

  Implicit Types e : expr.
  Implicit Types E : coPset.
  Implicit Types A B : lty2 Σ.

  Definition refines_def (E : coPset)
           (e e' : expr) (A : lty2 Σ) : iProp Σ :=
    (* TODO: refactor the quantifiers *)
    (∀ ρ, spec_ctx ρ -∗ (∀ j K, j ⤇ fill K e'
        ={E,⊤}=∗ WP e {{ v, ∃ v', j ⤇ fill K (of_val v') ∗ A v v' }}))%I.

  Definition refines_aux : seal refines_def. Proof. by eexists. Qed.
  Definition refines := unseal refines_aux.
  Definition refines_eq : refines = refines_def :=
    seal_eq refines_aux.

  Global Instance refines_ne E n :
    Proper ((=) ==> (=) ==> (dist n) ==> (dist n)) (refines E).
  Proof. rewrite refines_eq /refines_def. solve_proper. Qed.

  Global Instance refines_proper E  :
    Proper ((=) ==> (=) ==> (≡) ==> (≡)) (refines E).
  Proof. solve_proper_from_ne. Qed.

  Definition lty2_unit : lty2 Σ := Lty2 (λ w1 w2, ⌜ w1 = #() ∧ w2 = #() ⌝%I).
  Definition lty2_bool : lty2 Σ := Lty2 (λ w1 w2, ∃ b : bool, ⌜ w1 = #b ∧ w2 = #b ⌝)%I.
  Definition lty2_int : lty2 Σ := Lty2 (λ w1 w2, ∃ n : Z, ⌜ w1 = #n ∧ w2 = #n ⌝)%I.

  Definition lty2_arr (A1 A2 : lty2 Σ) : lty2 Σ := Lty2 (λ w1 w2,
    □ ∀ v1 v2, A1 v1 v2 -∗ refines ⊤ (App w1 v1) (App w2 v2) A2)%I.

  Definition lty2_ref (A : lty2 Σ) : lty2 Σ := Lty2 (λ w1 w2,
    ∃ l1 l2: loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (relocN .@ "ref" .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ₛ v2 ∗ A v1 v2))%I.

  Definition lty2_prod (A B : lty2 Σ) : lty2 Σ := Lty2 (λ w1 w2,
    ∃ v1 v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧
        A v1 v2 ∗ B v1' v2')%I.

  Definition lty2_sum (A B : lty2 Σ) : lty2 Σ := Lty2 (λ w1 w2,
    ∃ v1 v2, (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ A v1 v2)
          ∨  (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ B v1 v2))%I.

  Definition lty2_rec1 (C : lty2C Σ -n> lty2C Σ) (rec : lty2 Σ) : lty2 Σ :=
    Lty2 (λ w1 w2, ▷ C rec w1 w2)%I.
  Instance lty2_rec1_contractive C : Contractive (lty2_rec1 C).
  Proof.
    intros n. intros P Q HPQ.
    unfold lty2_rec1. intros w1 w2.
    apply bi.later_contractive.
    destruct n; try done.
    simpl in HPQ; simpl. f_equiv. by apply C.
  Qed.

  Definition lty2_rec (C : lty2C Σ -n> lty2C Σ) : lty2 Σ := fixpoint (lty2_rec1 C).

  Definition lty2_exists (C : lty2 Σ → lty2 Σ) : lty2 Σ := Lty2 (λ w1 w2,
    ∃ A, C A w1 w2)%I.

  (** The lty2 constructors are non-expansive *)
  Global Instance lty2_prod_ne n : Proper (dist n ==> dist n ==> dist n) lty2_prod.
  Proof. solve_proper. Qed.

  Global Instance lty2_sum_ne n : Proper (dist n ==> dist n ==> dist n) lty2_sum.
  Proof. solve_proper. Qed.

  Global Instance lty2_arr_ne n : Proper (dist n ==> dist n ==> dist n) lty2_arr.
  Proof. solve_proper. Qed.

  Global Instance lty2_rec_ne n : Proper (dist n ==> dist n)
       (lty2_rec : (lty2C Σ -n> lty2C Σ) -> lty2C Σ).
  Proof.
    intros F F' HF.
    unfold lty2_rec, lty2_car.
    apply fixpoint_ne=> X w1 w2.
    unfold lty2_rec1, lty2_car. cbn.
    f_equiv.
    apply lty2_car_ne; eauto.
  Qed.

  Lemma lty_rec_unfold (C : lty2C Σ -n> lty2C Σ) : lty2_rec C ≡ lty2_rec1 C (lty2_rec C).
  Proof. apply fixpoint_unfold. Qed.

End semtypes.

(** Nice notations *)
Notation "()" := lty2_unit : lty_scope.
Infix "→" := lty2_arr : lty_scope.
Infix "×" := lty2_prod (at level 80) : lty_scope.
Notation "'ref' A" := (lty2_ref A) : lty_scope.
Notation "∃ A1 .. An , C" :=
  (lty2_exists (λ A1, .. (lty2_exists (λ An, C%lty2)) ..)) : lty_scope.

Section semtypes_properties.
  Context `{relocG Σ}.

  (* The reference type relation is functional and injective.
     Thanks to Amin. *)
  Lemma interp_ref_funct E (A : lty2 Σ) (l l1 l2 : loc) :
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

  Lemma interp_ref_inj E (A : lty2 Σ) (l l1 l2 : loc) :
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

End semtypes_properties.

Notation "'REL' e1 '<<' e2 '@' E ':' A" :=
  (refines E e1%E e2%E (A)%lty2)
  (at level 100, E at next level, e1, e2 at next level,
   A at level 200,
   format "'[hv' 'REL'  e1  '/' '<<'  '/  ' e2  '@'  E  :  A ']'").
Notation "'REL' e1 '<<' e2 ':' A" :=
  (refines ⊤ e1%E e2%E (A)%lty2)
  (at level 100, e1, e2 at next level,
   A at level 200,
   format "'[hv' 'REL'  e1  '/' '<<'  '/  ' e2  :  A ']'").

(** Properties of the relational interpretation *)
Section related_facts.
  Context `{relocG Σ}.

  (* We need this to be able to open and closed invariants in front of logrels *)
  Lemma fupd_logrel E1 E2 e e' A :
    ((|={E1,E2}=> REL e << e' @ E2 : A)
     -∗ (REL e << e' @ E1 : A))%I.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "H". iIntros (ρ) "#Hs"; iIntros (j K) "Hj /=".
    iMod "H" as "H". iApply ("H" with "Hs Hj").
  Qed.

  Global Instance elim_fupd_logrel p E1 E2 e e' P A :
   (* TODO: DF: look at the booleans here *)
   ElimModal True p false (|={E1,E2}=> P) P
     (REL e << e' @ E1 : A) (REL e << e' @ E2: A).
  Proof.
    rewrite /ElimModal. intros _.
    iIntros "[HP HI]". iApply fupd_logrel.
    destruct p; simpl; rewrite ?bi.intuitionistically_elim;
    iMod "HP"; iModIntro; by iApply "HI".
  Qed.

  Global Instance elim_bupd_logrel p E e e' P A :
   ElimModal True p false (|==> P) P
     (REL e << e' @ E : A) (REL e << e' @ E : A).
  Proof.
    rewrite /ElimModal (bupd_fupd E).
    apply: elim_fupd_logrel.
  Qed.

  (* This + elim_modal_timless_bupd' is useful for stripping off laters of timeless propositions. *)
  Global Instance is_except_0_logrel E e e' A :
    IsExcept0 (REL e << e' @ E : A).
  Proof.
    rewrite /IsExcept0. iIntros "HL".
    iApply fupd_logrel. by iMod "HL".
  Qed.
End related_facts.

Section monadic.
  Context `{relocG Σ}.

  Lemma refines_bind K K' E A A' e e' :
    (REL e << e' @ E : A) -∗
    (∀ v v', A v v' -∗
      (REL fill K (of_val v) << fill K' (of_val v') : A')) -∗
    (REL fill K e << fill K' e' @ E : A').
  Proof.
    iIntros "Hm Hf".
    rewrite refines_eq /refines_def.
    iIntros (ρ) "#Hs". iSpecialize ("Hm" with "Hs").
    iIntros (j K₁) "Hj /=".
    rewrite -fill_app. iMod ("Hm" with "Hj") as "Hm".
    iModIntro. iApply wp_bind.
    iApply (wp_wand with "Hm").
    iIntros (v). iDestruct 1 as (v') "[Hj HA]".
    rewrite fill_app.
    by iMod ("Hf" with "HA Hs Hj") as "Hf/=".
  Qed.

  Lemma refines_ret E e1 e2 v1 v2 (A : lty2 Σ) :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    (|={E,⊤}=> A v1 v2) -∗ REL e1 << e2 @ E : A.
  Proof.
    iIntros (<-<-) "HA".
    rewrite refines_eq /refines_def.
    iIntros (ρ) "#Hs". simpl.
    iIntros (j K) "Hj /=".
    iMod "HA" as "HA". iModIntro.
    iApply wp_value. iExists _. by iFrame.
  Qed.

End monadic.
