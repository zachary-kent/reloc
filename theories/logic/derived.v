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

  Lemma refines_wand E e1 e2 A A' :
    (REL e1 << e2 @ E : A) -∗
    (∀ v1 v2, A v1 v2 ={⊤}=∗ A' v1 v2) -∗
    REL e1 << e2 @ E : A'.
  Proof.
    iIntros "He HAA".
    iApply (refines_bind [] [] with "He").
    iIntros (v v') "HA /=". iApply refines_ret.
    by iApply "HAA".
  Qed.

  Lemma refines_arrow (f x f' x' : binder) (eb eb' : expr) A A' :
    □(∀ v1 v2 : val, □(REL of_val v1 << of_val v2 : A) -∗
      REL App (RecV f x eb) (of_val v1) << App (RecV f' x' eb') (of_val v2) : A') -∗
    REL (RecV f x eb) << (RecV f' x' eb') : (A → A')%lty2.
  Proof.
    iIntros "#H".
    iApply refines_arrow_val; eauto.
    iAlways. iIntros (v1 v2) "#HA".
    iApply "H". iAlways.
    by iApply refines_ret.
  Qed.

End rules.
