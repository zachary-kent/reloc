(* Partial bijections ghost state.

Originally from: "A Logical Relation for Monadic Encapsulation of State: Proving contextual equivalences in the presence of runST"
by Amin Timany, Léo Stefanesco, Morten Krogh-Jespersen, Lars Birkedal *)
From iris.algebra Require Import auth gset.
From iris.base_logic Require Export auth invariants.
From iris.proofmode Require Import tactics.
Import uPred.

Section PBij.
Variable (A B : Type).
Context `{Countable A, Countable B}.
Definition bijective (g : gset (A * B)) :=
  ∀ x y, (x, y) ∈ g → (∀ z, (x, z) ∈ g → z = y) ∧ (∀ z, (z, y) ∈ g → z = x).

Lemma empty_bijective : bijective ∅.
Proof. by intros x y Hxy; apply not_elem_of_empty in Hxy. Qed.

Lemma bijective_extend g l l' :
  bijective g → (∀ y, (l, y) ∉ g) → (∀ y, (y, l') ∉ g) →
  bijective (({[(l, l')]} : gset (A * B)) ∪ g).
Proof.
  intros bij Hl Hl' x y Hxy.
  apply elem_of_union in Hxy; destruct Hxy as [Hxy|Hxy].
  - apply elem_of_singleton_1 in Hxy; inversion Hxy; subst.
    split; intros z Hz; apply elem_of_union in Hz; destruct Hz as [Hz|Hz];
      try (apply elem_of_singleton_1 in Hz; inversion Hz; subst); trivial;
        try (by apply Hl in Hz); try (by apply Hl' in Hz).
  - assert (x ≠ l) by (by intros Heql; subst; apply Hl in Hxy).
    assert (y ≠ l') by (by intros Heql'; subst; apply Hl' in Hxy).
    apply bij in Hxy; destruct Hxy as [Hxy1 Hx2].
    split; intros z Hz; apply elem_of_union in Hz; destruct Hz as [Hz|Hz];
      try (apply elem_of_singleton_1 in Hz; inversion Hz; subst); trivial;
        try match goal with H : ?A = ?A  |- _ => by contradict H end;
        auto.
Qed.

Lemma bij_eq_iff g l1 l2 l1' l2' :
  bijective g → ((l1, l1') ∈ g) → ((l2, l2') ∈ g) → l1 = l2 ↔ l1' = l2'.
Proof.
  intros bij Hl1 Hl2; split => Hl1eq; subst;
    by pose proof (bij _ _ Hl1) as Hb1; apply Hb1 in Hl2.
Qed.

Definition bijUR := gsetUR (A * B).
Class pBijPreG Σ := PBijPreG
{ pBijPreG_inG :> authG Σ bijUR }.
Class pBijG Σ := PBijG
{ pBijG_inG :> authG Σ bijUR
; pBijG_name : gname }.
Definition pBijΣ : gFunctors := #[ authΣ bijUR ].
Global Instance subG_pBijΣ {Σ} : subG pBijΣ Σ → pBijPreG Σ.
Proof. solve_inG. Qed.

Section logic.
  Context `{pBijPreG Σ}.

  Definition BIJ_def γ (L : bijUR) : iProp Σ :=
    (own γ (● L) ∗ ⌜bijective L⌝)%I.
  Definition BIJ_aux : { x | x = @BIJ_def }. by eexists. Qed.
  Definition BIJ := proj1_sig BIJ_aux.
  Definition BIJ_eq : @BIJ = @BIJ_def := proj2_sig BIJ_aux.
  Global Instance BIJ_timeless γ L : Timeless (BIJ γ L).
  Proof. rewrite BIJ_eq /BIJ_def. apply _. Qed.

  Lemma alloc_empty_bij : ⊢ |==> ∃ γ, BIJ γ ∅.
  Proof.
    rewrite BIJ_eq /BIJ_def.
    iMod (own_alloc (● (∅ : bijUR))) as (γ) "H".
    { by apply auth_auth_valid. }
    iModIntro; iExists _; iFrame. iPureIntro. apply empty_bijective.
  Qed.

  Definition inBij_def γ (a : A) (b : B) :=
    own γ (◯ ({[ (a, b) ]} : gset (A * B))).
  Definition inBij_aux : { x | x = @inBij_def }. by eexists. Qed.
  Definition inBij := proj1_sig inBij_aux.
  Definition inBij_eq : @inBij = @inBij_def := proj2_sig inBij_aux.

  Global Instance inBij_timeless γbij l l' : Timeless (inBij γbij l l').
  Proof. rewrite inBij_eq /inBij_def. apply _. Qed.

  Global Instance inBij_persistent γbij l l' : Persistent (inBij γbij l l').
  Proof. rewrite inBij_eq /inBij_def. apply _. Qed.

  Lemma bij_alloc (γ : gname) (L : gset (A * B)) a b :
    (∀ y, (a, y) ∉ L) → (∀ x, (x, b) ∉ L) →
    BIJ γ L ==∗
    BIJ γ (({[(a, b)]} : gset (A * B)) ∪ L) ∗ inBij γ a b.
  Proof.
    iIntros (Ha Hb) "HL"; rewrite BIJ_eq /BIJ_def inBij_eq /inBij_def.
    iDestruct "HL" as "[HL HL2]"; iDestruct "HL2" as %Hbij.
    iMod (own_update with "HL") as "HL".
    - apply auth_update_alloc.
      apply (gset_local_update _ _ (({[(a, b)]} : gset (A * B)) ∪ L)).
      apply union_subseteq_r.
    - rewrite -gset_op_union auth_frag_op !own_op.
      iDestruct "HL" as "[$ [$ _]]".
      iModIntro. iPureIntro.
      by apply bijective_extend.
  Qed.

  Lemma bij_alloc_alt (γ : gname) (L : gset (A * B)) a b :
    ¬(∃ y, (a, y) ∈ L) → ¬(∃ x, (x, b) ∈ L) →
    BIJ γ L ==∗
    BIJ γ (({[(a, b)]} : gset (A * B)) ∪ L) ∗ inBij γ a b.
  Proof.
    intros Ha Hb; eapply bij_alloc; naive_solver.
  Qed.

  Lemma bij_agree γ L (a a' : A) (b b' : B) :
    BIJ γ L -∗
    inBij γ a b -∗
    inBij γ a' b' -∗
    ⌜a = a' ↔ b = b'⌝.
  Proof.
    iIntros "HL H1 H2". rewrite BIJ_eq /BIJ_def inBij_eq /inBij_def.
    iDestruct "HL" as "[HL HL1]"; iDestruct "HL1" as %HL.
    iDestruct (own_valid_2 with "HL H1") as %Hv1%auth_both_valid.
    iDestruct (own_valid_2 with "HL H2") as %Hv2%auth_both_valid.
    iPureIntro.
    destruct Hv1 as [Hv1 _]; destruct Hv2 as [Hv2 _].
    apply gset_included, elem_of_subseteq_singleton in Hv1;
      apply gset_included, elem_of_subseteq_singleton in Hv2.
    eapply bij_eq_iff; eauto.
  Qed.

End logic.

End PBij.

Arguments BIJ {_} {_} {_} {_} {_} {_} {_} {_} γ L.
Arguments inBij {_} {_} {_} {_} {_} {_} {_} {_} γ a b.
