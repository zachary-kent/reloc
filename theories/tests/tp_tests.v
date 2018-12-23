From iris.proofmode Require Import tactics.
From reloc.logic Require Export spec_rules proofmode.spec_tactics.
Set Default Proof Using "Type".
Import lang.

Section test.
Context `{relocG Σ}.

Lemma test1 E1 j K (l : loc) (n : nat) ρ :
  nclose specN ⊆ E1 →
  j ⤇ fill K (App (Lam "x" (Store #l (Var "x"))) (Load (# l))) -∗
  spec_ctx ρ -∗
  l ↦ₛ #n ={E1}=∗ True.
Proof.
  iIntros (?) "Hj #? Hl".
  tp_load j. tp_normalise j.
  tp_closure j. tp_normalise j.
  tp_lam j. tp_normalise j.
  tp_store j. done.
Qed.

End test.
