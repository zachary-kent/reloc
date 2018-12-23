From iris.proofmode Require Import tactics.
From reloc.logic Require Export spec_rules proofmode.spec_tactics.
Set Default Proof Using "Type".
Import lang.

Section test.
Context `{relocG Σ}.

(* store, load, and some pure reductions *)
Lemma test1 E1 j K (l : loc) (n : nat) ρ :
  nclose specN ⊆ E1 →
  spec_ctx ρ -∗
  j ⤇ fill K ((λ: "x", #l <- "x" + #1) !#l)%E -∗
  l ↦ₛ #n
  ={E1}=∗ l ↦ₛ #(n+1) ∗ j ⤇ fill K #().
Proof.
  iIntros (?) "#? Hj Hl".
  tp_load j. tp_normalise j.
  tp_closure j. tp_normalise j.
  tp_lam j. tp_normalise j.
  tp_binop j. tp_normalise j.
  tp_store j. by iFrame.
Qed.

(* CAS *)
Lemma test2 E1 j K (l : loc) (n : nat) ρ :
  nclose specN ⊆ E1 →
  spec_ctx ρ -∗
  j ⤇ fill K (CAS #l #2 #n;; CAS #l #3 (#n*#2)) -∗
  l ↦ₛ #3
  ={E1}=∗ l ↦ₛ #(n*2) ∗ j ⤇ fill K #true.
Proof.
  iIntros (?) "#? Hj Hl".
  tp_cas_fail j. tp_normalise j.
  tp_closure j. tp_normalise j.
  tp_seq j. tp_normalise j.
  tp_binop j. tp_normalise j.
  tp_cas_suc j. by iFrame.
Qed.

(* fork *)
Lemma test3 E1 j e K (l : loc) (n : nat) ρ :
  nclose specN ⊆ E1 →
  spec_ctx ρ -∗
  j ⤇ fill K (Fork e)
  ={E1}=∗ ∃ i, i ⤇ e ∗ j ⤇ fill K #().
Proof.
  iIntros (?) "#? Hj".
  tp_fork j. Undo.
  tp_fork j as i. eauto with iFrame.
Qed.

(* alloc *)
Lemma test4 E1 j K (n : nat) ρ :
  nclose specN ⊆ E1 →
  spec_ctx ρ -∗
  j ⤇ fill K (ref #3)
  ={E1}=∗ ∃ l, l ↦ₛ #3 ∗ j ⤇ fill K #l.
Proof.
  iIntros (?) "#? Hj".
  tp_alloc j as l "Hl".
  iExists l. by iFrame.
Qed.


End test.

(* Section test2. *)
(* Context `{logrelG Σ}. *)
(* (* TODO: Coq complains if I make it a section variable *) *)
(* Axiom (steps_release_test : forall E ρ j K (l : loc) (b : bool), *)
(*     nclose specN ⊆ E → *)
(*     spec_ctx ρ -∗ l ↦ₛ #b -∗ j ⤇ fill K (App #() #l) *)
(*     ={E}=∗ j ⤇ fill K #() ∗ l ↦ₛ #false). *)

(* Theorem test_apply E ρ j (b : bool) K l: *)
(*   nclose specN ⊆ E → *)
(*   spec_ctx ρ -∗  *)
(*   l ↦ₛ #b -∗ j ⤇ fill K (App #() #l) *)
(*   -∗ |={E}=> True. *)
(* Proof. *)
(*   iIntros (?) "#Hs Hst Hj". *)
(*   tp_apply j steps_release_test with "Hst" as "Hl". *)
(*   done. *)
(* Qed. *)

(* End test2. *)
