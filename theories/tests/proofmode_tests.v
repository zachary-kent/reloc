From iris.proofmode Require Import tactics.
From reloc.logic.proofmode Require Export tactics.
From iris.heap_lang Require Import lang notation.

Section test.
Context `{relocG Σ}.

Definition EqI : lty2 := Lty2 (λ v1 v2, ⌜v1 = v2⌝)%I.
(* Pure reductions *)
Lemma test1 Γ A P t :
  ▷ P -∗
  (P -∗ Γ ⊨ #4 << t : A) -∗
  Γ ⊨ (#2 + #2) << (λ: <>, t) #() : A.
Proof.
  iIntros "HP Ht".
  rel_bind_l #2. Undo.
  rel_pure_l (_ + _)%E. Undo.
  rel_pure_l.
  repeat rel_pure_r.
  by iApply "Ht".
Qed.

Lemma test2 E Γ :
  ↑specN ⊆ E →
  (|={E,⊤}=> True) -∗
  {E;Γ} ⊨ (#2 + #2) << (#5 - #1) : EqI.
Proof.
  intros ?.
  iIntros "Hclose".
  rel_pure_l.
  rel_pure_r.
  rel_values.
  by iMod "Hclose".
Qed.

(* testing rel_apply_l/r and rel_load_l/r *)
Lemma test3 l r Γ :
  ▷ l ↦ #3 -∗
  r ↦ₛ #4 -∗
  Γ ⊨ (!#l;;!#l+#1) << (!#r;;#0+!#r) : EqI.
Proof.
  iIntros "Hl Hr".
  rel_apply_r (refines_load_r with "Hr").
  iIntros "Hr".
  rel_load_l.
  do 2 rel_pure_r.
  do 2 rel_pure_l.
  rel_apply_l refines_load_l. iModIntro. iExists _; iFrame.
  iNext. iIntros "Hl". simpl.
  rel_pure_l.
  rel_load_r.
  rel_pure_r.
  rel_values.
Qed.

(* testing (atomic) load with invariants *)
Lemma test4 l r Γ N :
  inv N (l ↦ #3) -∗
  r ↦ₛ #4 -∗
  Γ ⊨ (!#l;;!#l+#1) << (!#r;;#0+!#r) : EqI.
Proof.
  iIntros "#IN Hr".
  repeat (rel_load_r || rel_pure_r).
  rel_load_l. iInv N as "?" "Hcl". iModIntro. iExists _; iFrame.
  iNext. iIntros "Hl". iMod ("Hcl" with "Hl") as "_".
  repeat (rel_pure_l || rel_load_l).
  iInv N as "?" "Hcl". iModIntro. iExists _; iFrame.
  iNext. iIntros "Hl". iMod ("Hcl" with "Hl") as "_".
  rel_pure_l.
  rel_values.
Qed.

End test.
