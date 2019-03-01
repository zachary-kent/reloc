(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Compataibility rules *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import list.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Import proofmode.
From reloc.logic Require Export model rules.
From reloc.logic Require Import proofmode.tactics proofmode.spec_tactics model.

Section compatibility.
  Context `{relocG Σ}.

  Local Ltac value_case :=
    try rel_pure_l; try rel_pure_r; rel_values.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(Hv):=
    rel_bind_l e1;
    rel_bind_r e2;
    iApply (refines_bind with IH);
    iIntros (v w) Hv; simpl.

  Lemma refines_pair e1 e2 e1' e2' A B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1, e2) << (e1', e2') : A × B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" v2 v2' "Hvv2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "Hvv1".
    value_case.
    iExists _, _, _, _; eauto.
  Qed.

  Lemma refines_app e1 e2 e1' e2' A B :
    (REL e1 << e1' : (A → B)) -∗
    (REL e2 << e2' : A) -∗
    REL App e1 e2 << App e1' e2' : B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" v v' "Hvv".
    rel_bind_ap e1 e1' "IH1" f f' "Hff".
    rewrite interp_val_arrow. by iApply "Hff".
  Qed.

  Lemma refines_fork e e' E :
    ↑relocN ⊆ E →
    (REL e << e' @ E : ()) -∗
    REL Fork e << Fork e' @ E : ().
  Proof.
    iIntros (?) "IH".
    rewrite refines_eq /refines_def.
    iIntros (ρ) "#Hρ"; iIntros (j K) "Hj /=".
    tp_fork j as i "Hi".
    iSpecialize ("IH" with "Hρ"). unfold interp_expr.
    iMod ("IH" $! i [] with "Hi") as "IH".
    iApply (wp_fork with "[-Hj]").
    - iNext. iApply (wp_wand with "IH"). eauto.
    - iExists #(); eauto.
  Qed.

End compatibility.
