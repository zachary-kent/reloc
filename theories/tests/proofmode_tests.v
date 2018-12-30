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

End test.
