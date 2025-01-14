From iris.proofmode Require Import proofmode.
From reloc.logic.proofmode Require Export spec_tactics tactics.
From iris.heap_lang Require Import lang notation.

Section test.
Context `{relocG Σ}.

Definition EqI : lrel Σ := LRel (λ v1 v2, ⌜v1 = v2⌝)%I.
(* Pure reductions *)
Lemma test1 A P (t: expr) :
  ▷ P -∗
  (P -∗ REL #4 << t : A) -∗
  REL (#2 + #2) << (λ: <>, t) #() : A.
Proof.
  iIntros "HP Ht".
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
  rel_fork_r i as "Hi".
  repeat rel_pure_r.
  tp_store i.
  rel_load_r.
  rel_values.
Qed.


Lemma test_xchg_1 l1 l2 (v1 v2 : val) (A : lrel Σ) :
  l1 ↦ v1 -∗
  l2 ↦ₛ v2 -∗
  (l1 ↦ #3 -∗ l2 ↦ₛ #3 -∗ A v1 v2) -∗
  REL Xchg #l1 #3 << Xchg #l2 #3 : A.
Proof.
  iIntros "Hl1 Hl2 H".
  rel_xchg_l. rel_xchg_r. rel_values.
  iModIntro. iApply ("H" with "Hl1 Hl2").
Qed.

Lemma test_xchg_2 l1 l2 (v1 v2 : val) (A : lrel Σ) :
  l1 ↦ v1 -∗
  l2 ↦ₛ v2 -∗
  (l1 ↦ #3 -∗ l2 ↦ₛ #3 -∗ A v1 v2) -∗
  REL Xchg #l1 #3 << (let: "x" := !#l2 in #l2 <- #3;; "x") : A.
Proof.
  iIntros "Hl1 Hl2 H".
  rel_xchg_l. rel_load_r. rel_pures_r.
  rel_store_r. rel_pures_r. rel_values.
  iModIntro. iApply ("H" with "Hl1 Hl2").
Qed.

End test.

