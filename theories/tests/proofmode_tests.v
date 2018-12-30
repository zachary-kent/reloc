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
  Γ ⊨ (#2 + #2) << t : A.
Proof.
  iIntros "HP Ht".
  rel_bind_l #2. Undo.
  rel_pure_l (_ + _)%E.
  by iApply "Ht".
Qed.

Lemma test2 E Γ :
  (|={E,⊤}=> True) -∗
  {E;Γ} ⊨ (#2 + #2) << #4 : EqI.
Proof.
  iIntros "Hclose".
  rel_pure_l (_ + _)%E.
  iApply refines_ret.
  by iMod "Hclose".
Qed.

End test.
