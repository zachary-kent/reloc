(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Derived ReLoC rules *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import list.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Import proofmode.
From reloc.logic Require Export model rules.

Section rules.
  Context `{relocG Σ}.
  Implicit Types A : lty2 Σ.

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

  Lemma refines_arrow Γ (f x f' x' : binder) (e e' eb eb' : expr) A A' :
    e = of_val (RecV f x eb)%E →
    e' = of_val (RecV f' x' eb')%E →
    □(∀ v1 v2 : val, □(Γ ⊨ of_val v1 << of_val v2 : A) -∗
      Γ ⊨ App e (of_val v1) << App e' (of_val v2) : A') -∗
    Γ ⊨ e << e' : (A → A')%lty2.
  Proof.
    iIntros (??) "#H".
    iApply refines_arrow_val; eauto.
    iAlways. iIntros (v1 v2) "#HA".
    iApply "H". iAlways.
    by iApply refines_ret.
  Qed.

End rules.
