From iris.algebra Require Import excl.
From reloc.typing Require Import types interp fundamental.
From reloc Require Export proofmode.

Definition newlock : val := λ: <>, ref #false.
Definition acquire : val := rec: "acquire" "x" :=
  if: CAS "x" #false #true
  then #()
  else "acquire" "x".

Definition release : val := λ: "x", "x" <- #false.
Definition with_lock : val := λ: "e" "l" "x",
  acquire "l";;
  let: "v" := "e" "x" in
  release "l";; "v".

Definition LockType := Tref TBool.

(* Hint Unfold LockType : typeable. *)

(* Lemma newlock_type Γ : typed Γ newlock (TArrow TUnit LockType). *)
(* Proof. solve_typed. Qed. *)

(* Hint Resolve newlock_type : typeable. *)

(* Lemma acquire_type Γ : typed Γ acquire (TArrow LockType TUnit). *)
(* Proof. solve_typed. Qed. *)

(* Hint Resolve acquire_type : typeable. *)

(* Lemma release_type Γ : typed Γ release (TArrow LockType TUnit). *)
(* Proof. solve_typed. Qed. *)

(* Hint Resolve release_type : typeable. *)

(* Lemma with_lock_type Γ τ τ' : *)
(*   typed Γ with_lock (TArrow (TArrow τ τ') (TArrow LockType (TArrow τ τ'))). *)
(* Proof. solve_typed. Qed. *)

(* Hint Resolve with_lock_type : typeable. *)

Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitC)].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section lockG_rules.
  Context `{!lockG Σ, !relocG Σ} (N: namespace).

  Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜lk = #l⌝ ∧ inv N (lock_inv γ l R))%I.

  Definition locked (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Global Instance lock_inv_ne γ l : NonExpansive (lock_inv γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne l : NonExpansive (is_lock γ l).
  Proof. solve_proper. Qed.

  Global Instance is_lock_persistent γ l R : Persistent (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Lemma refines_newlock_l (R : iProp Σ) Γ K t A :
    R -∗
    ▷(∀ (lk : loc) γ, is_lock γ #lk R
      -∗ (Γ ⊨ fill K (of_val #lk) << t: A)) -∗
    Γ ⊨ fill K (newlock #()) << t: A.
  Proof.
    iIntros "HR Hlog".
    unfold newlock. unlock.
    rel_pure_l.
    rel_alloc_l l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l R) with "[-Hlog]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iApply "Hlog". iExists l. eauto.
  Qed.

  Lemma refines_release_l (R : iProp Σ) (lk : loc) γ Γ K t A :
    is_lock γ #lk R -∗
    locked γ -∗
    R -∗
    ▷(Γ ⊨ fill K (of_val #()) << t: A) -∗ (* TODO: why do I have to type `of_val` here? *)
    Γ ⊨ fill K (release #lk) << t: A.
  Proof.
    iIntros "Hlock Hlocked HR Hlog".
    iDestruct "Hlock" as (l) "[% #?]"; simplify_eq.
    unlock release. simpl.
    rel_let_l.
    rel_store_l_atomic.
    iInv N as (b) "[Hl _]" "Hclose".
    iModIntro. iExists _. iFrame.
    iNext. iIntros "Hl".
    iMod ("Hclose" with "[-Hlog]").
    { iNext. iExists false. by iFrame. }
    iApply "Hlog".
  Qed.

  Lemma refines_acquire_l (R : iProp Σ) (lk : loc) γ Γ K t A :
    is_lock γ #lk R -∗
    ▷(locked γ -∗ R -∗ Γ ⊨ fill K (of_val #()) << t: A) -∗
    Γ ⊨ fill K (acquire #lk) << t: A.
  Proof.
    iIntros "#Hlock Hlog".
    iLöb as "IH".
    unlock acquire. simpl.
    rel_rec_l.
    iDestruct "Hlock" as (l) "[% #?]". simplify_eq.
    rel_cas_l_atomic.
    iInv N as (b) "[Hl HR]" "Hclose".
    iModIntro. iExists _. iFrame.
    iSplit.
    - iIntros (?). iNext. iIntros "Hl".
      assert (b = true) as ->. { destruct b; congruence. }
      rel_if_l.
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      by iApply "IH".
    - iIntros (?). simplify_eq.
      iNext. iIntros "Hl".
      rel_if_l.
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iDestruct "HR" as "[Hlocked HR]".
      iApply ("Hlog" with "Hlocked HR").
  Qed.

End lockG_rules.

Section lock_rules_r.
  Context `{relocG Σ}.
  Variable (E : coPset).

  Lemma refines_newlock_r Γ K t A
    (Hcl : nclose specN ⊆ E) :
    (∀ l : loc, l ↦ₛ #false -∗ {E;Γ} ⊨ t << fill K (of_val #l) : A) -∗
    {E;Γ} ⊨ t << fill K (newlock #()): A.
  Proof.
    iIntros "Hlog".
    unfold newlock. unlock.
    rel_rec_r.
    rel_alloc_r l as "Hl".
    iApply ("Hlog" with "Hl").
  Qed.

  Global Opaque newlock.

  Transparent acquire.

  Lemma refines_acquire_r Γ K l t A
    (Hcl : nclose specN ⊆ E) :
    l ↦ₛ #false -∗
    (l ↦ₛ #true -∗ {E;Γ} ⊨ t << fill K (of_val #()) : A) -∗
    {E;Γ} ⊨ t << fill K (acquire #l) : A.
  Proof.
    iIntros "Hl Hlog".
    unfold acquire. unlock.
    rel_rec_r.
    rel_cas_suc_r. simpl.
    rel_if_r.
    by iApply "Hlog".
  Qed.

  Global Opaque acquire.

  Transparent release.
  Lemma refines_release_r Γ K l t A (b : bool)
    (Hcl : nclose specN ⊆ E) :
    l ↦ₛ #b -∗
    (l ↦ₛ #false -∗ {E;Γ} ⊨ t << fill K (of_val #()) : A) -∗
    {E;Γ} ⊨ t << fill K (release #l) : A.
  Proof.
    iIntros "Hl Hlog".
    unfold release. unlock.
    rel_rec_r.
    rel_store_r.
    by iApply "Hlog".
  Qed.

  Global Opaque release.

End lock_rules_r.
