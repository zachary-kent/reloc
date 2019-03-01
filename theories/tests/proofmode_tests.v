From iris.proofmode Require Import tactics.
From reloc.logic.proofmode Require Export spec_tactics tactics.
From iris.heap_lang Require Import lang notation.

Section test.
Context `{relocG Σ}.

Definition EqI : lty2 Σ := Lty2 (λ v1 v2, ⌜v1 = v2⌝)%I.
(* Pure reductions *)
Lemma test1 A P t :
  ▷ P -∗
  (P -∗ REL #4 << t : A) -∗
  REL (#2 + #2) << (λ: <>, t) #() : A.
Proof.
  iIntros "HP Ht".
  rel_bind_l #2. Undo.
  rel_pure_l (_ + _)%E. Undo.
  rel_pure_l. repeat rel_pure_r.
  by iApply "Ht".
Qed.

Lemma test2 E :
  ↑specN ⊆ E →
  (|={E,⊤}=> True) -∗
  REL (#2 + #2) << (#5 - #1) @ E : EqI.
Proof.
  intros ?.
  iIntros "Hclose".
  rel_pure_l.
  rel_pure_r.
  rel_values.
  by iMod "Hclose".
Qed.

(* testing rel_apply_l/r and rel_load_l/r *)
Lemma test3 l r :
  ▷ l ↦ #3 -∗
  r ↦ₛ #4 -∗
  REL (!#l;;!#l+#1) << (!#r;;#0+!#r) : EqI.
Proof.
  iIntros "Hl Hr".
  rel_apply_r (refines_load_r with "Hr").
  iIntros "Hr".
  rel_load_l.
  progress repeat rel_pure_r.
  progress repeat rel_pure_l.
  rel_apply_l refines_load_l. iModIntro. iExists _; iFrame.
  iNext. iIntros "Hl". simpl.
  rel_pure_l.
  rel_load_r.
  rel_pure_r.
  rel_values.
Qed.

(* testing (atomic) load with invariants *)
Lemma test4 l r N :
  inv N (l ↦ #3) -∗
  r ↦ₛ #4 -∗
  REL (!#l;;!#l+#1) << (!#r;;#0+!#r) : EqI.
Proof.
  iIntros "#IN Hr".
  repeat (rel_load_r || rel_pure_r).
  rel_load_l_atomic. iInv N as "?" "Hcl". iModIntro. iExists _; iFrame.
  iNext. iIntros "Hl". iMod ("Hcl" with "Hl") as "_".
  repeat rel_pure_l. rel_load_l_atomic.
  iInv N as "?" "Hcl". iModIntro. iExists _; iFrame.
  iNext. iIntros "Hl". iMod ("Hcl" with "Hl") as "_".
  rel_pure_l.
  rel_values.
Qed.

(* testing fork and store *)
Lemma test5 l r N :
  inv N (l ↦ #3) -∗
  r ↦ₛ #4 -∗
  REL (let: "x" := #1 + (Fork (#l <- #3);; !#l) in "x")
  << (#r <- #0;; Fork (#r <- #4);; !#r) : EqI.
Proof.
  iIntros "#IN Hr".
  rel_fork_l. iModIntro. iSplitR.
  { iNext. iInv N as "Hl" "Hcl".
    iApply (wp_store with "Hl"). iNext. iIntros "Hl".
    by iApply "Hcl". }
  iNext. do 2 rel_pure_l.
  rel_load_l_atomic. iInv N as "?" "Hcl". iModIntro. iExists _; iFrame.
  iNext. iIntros "Hl". iMod ("Hcl" with "Hl") as "_".
  repeat rel_pure_l.
  rel_store_r. do 2 rel_pure_r.
  rel_fork_r as i "Hi".
  repeat rel_pure_r.
  iApply refines_spec_ctx. iDestruct 1 as (?) "#?".
  tp_store i.
  rel_load_r.
  rel_values.
Qed.

End test.

