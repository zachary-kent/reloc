(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Derived ReLoC rules *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import list.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Import proofmode.
From reloc.logic Require Export model rules.

Section rules.
  Context `{relocG Σ}.
  Implicit Types A : lty2.

  Lemma refines_weaken E Γ e1 e2 A A' :
    (∀ v1 v2, A v1 v2 ={⊤}=∗ A' v1 v2) -∗
    ({E;Γ} ⊨ e1 << e2 : A) -∗
    {E;Γ} ⊨ e1 << e2 : A'.
  Proof.
    iIntros "HAA He".
    iApply (refines_bind [] [] with "He").
    iIntros (v v') "HA /=". iApply refines_ret.
    by iApply "HAA".
  Qed.
End rules.
