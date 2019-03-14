(* ReLoC -- Relational logic for fine-grained concurrency *)
(** (In)equational theory of erratic choice operator (`or`). *)
From reloc Require Export reloc lib.Y (* for bot *).
Set Default Proof Using "Type".

(** (Binary) non-determinism can be simluated with concurrency. In
this file we derive the algebraic laws for parallel "or"/demonic
choice combinator. In particular, we show the following (≤ stands for
contextual refinement and ≃ stands for contextual equivalence):

 - v1 () ≤ v1 or v2           choice on the RHS
 - v or v ≃ v ()              idempotency
 - v1 or v2 ≃ v2 or v1        commutativity
 - v or (λ_, ⊥) ≃ v ()       ⊥ is a unit
 - v1 or (λ_, v2 or v3)       associativity
   ≃ (λ_, v1 or v2) or v3

 where every v_i is thunk of type (() → τ). *)

Definition or : val := λ: "e1" "e2",
  let: "x" := ref #0 in
  Fork ("x" <- #1);;
  if: !"x" = #0
  then "e1" #()
  else "e2" #().

Section rules.
  Context `{relocG Σ}.

  (** Symbolic execution rule for the LHS *)
  Definition or_inv x : iProp Σ :=
    (x ↦ #0 ∨ x ↦ #1)%I.
  Definition orN := nroot .@ "orN".
  Ltac close_inv := iNext; (iLeft + iRight); by iFrame.

  Lemma or_refines_l K (v1 v2 : val) t A :
    ((REL fill K (v1 #()) << t : A)
     ∧ (REL fill K (v2 #()) << t : A)) -∗
    REL fill K (or v1 v2) << t : A.
  Proof.
    iIntros "H".
    rel_rec_l. repeat rel_pure_l.
    rel_alloc_l x as "Hx".
    iMod (inv_alloc orN _ (or_inv x) with "[Hx]") as "#Hinv";
      first close_inv.
    repeat rel_pure_l.
    rel_fork_l. iModIntro. iNext. iSplitR.
    { iApply wp_atomic.
      iInv orN as "[? | ?]" "Hcl"; iModIntro; wp_store;
        iApply "Hcl"; close_inv. }
    repeat rel_pure_l. rel_load_l_atomic.
    iInv orN as "[Hx | Hx]" "Hcl"; iModIntro;
      iExists _; iFrame; iNext; iIntros "Hx";
      (iMod ("Hcl" with "[Hx]") as "_"; first close_inv).
    - repeat rel_pure_l.
      iDestruct "H" as "[$ _]".
    - repeat rel_pure_l.
      iDestruct "H" as "[_ $]".
  Qed.

  (** Symbolic execution rule for the RHS *)
  Lemma or_refines_r K (v1 v2 : val) e A :
    ((REL e << fill K (v1 #()) : A)
     ∨ (REL e << fill K (v2 #()) : A)) -∗
    REL e << fill K (or v1 v2) : A.
  Proof.
    iIntros "H".
    rel_rec_r. repeat rel_pure_r.
    rel_alloc_r x as "Hx".
    repeat rel_pure_r.
    rel_fork_r j as "Hj".
    repeat rel_pure_r.
    iDestruct "H" as "[H | H]".
    - rel_load_r. repeat rel_pure_r. eauto with iFrame.
    - iApply refines_spec_ctx. (* TODO: get rid of this *)
      iDestruct 1 as (ρ) "#Hρ".
      tp_store j.
      rel_load_r. repeat rel_pure_r. eauto with iFrame.
  Qed.

  Opaque or.

  (** Compatibility rule *)
  Lemma or_compatible e1 e2 e1' e2' A :
    (REL e1 << e1' : () → A) -∗
    (REL e2 << e2' : () → A) -∗
    REL or e1 e2 << or e1' e2' : A.
  Proof.
    iIntros "H1 H2".
    rel_bind_l e2. rel_bind_r e2'.
    iApply (refines_bind with "H2").
    iIntros (v2 v2') "#Hv2".
    rel_bind_l e1. rel_bind_r e1'.
    iApply (refines_bind with "H1").
    iIntros (v1 v1') "#Hv1". iSimpl.
    rel_apply_l or_refines_l. iSplit.
    - rel_apply_r or_refines_r. iLeft.
      iApply refines_app.
      + iApply refines_ret. by iApply "Hv1".
      + rel_values.
    - rel_apply_r or_refines_r. iRight.
      iApply refines_app.
      + iApply refines_ret. by iApply "Hv2".
      + rel_values.
  Qed.

  (** Choice on the RHS *)
  Lemma or_choice_1_r (v1 v1' v2 : val) A :
    (REL v1 << v1' : () → A) -∗
    REL v1 #() << or v1' v2 : A.
  Proof.
    iIntros "H".
    rel_apply_r or_refines_r. iLeft.
    iApply (refines_app with "H").
    rel_values.
  Qed.

  (** Idempotence *)
  Lemma or_idemp_r (v v' : val) A :
    (REL v << v' : () → A) -∗
    REL v #() << or v' v' : A.
  Proof.
    iIntros "H".
    rel_apply_r or_refines_r. iLeft.
    iApply (refines_app with "H").
    rel_values.
  Qed.

  Lemma or_idemp_l (v v' : val) A :
    (REL v << v' : () → A) -∗
    REL or v v << v' #() : A.
  Proof.
    iIntros "H".
    rel_apply_l or_refines_l.
    iSplit; iApply (refines_app with "H"); rel_values.
  Qed.

  (** Commutativity *)
  Lemma or_comm (v1 v2 v1' v2' : val) A :
    (REL v1 << v1' : () → A) -∗
    (REL v2 << v2' : () → A) -∗
    REL or v1 v2 << or v2' v1' : A.
  Proof.
    iIntros "H1 H2".
    rel_apply_l or_refines_l. iSplit.
    - rel_apply_r or_refines_r. iRight.
      iApply (refines_app with "H1").
      rel_values.
    - rel_apply_r or_refines_r. iLeft.
      iApply (refines_app with "H2").
      rel_values.
  Qed.

  (** Bottom is the unit *)
  Lemma or_bot_l (v v' : val) A :
    (REL v << v' : () → A) -∗
    REL or v bot << v' #() : A.
  Proof.
    iIntros "H".
    rel_apply_l or_refines_l. iSplit.
    - iApply (refines_app with "H"). rel_values.
    - rel_apply_l bot_l.
  Qed.

  Lemma or_bot_r (v v' : val) A :
    (REL v << v' : () → A) -∗
    REL v #() << or v' bot : A.
  Proof.
    iIntros "H".
    rel_apply_r or_refines_r.
    iLeft. iApply (refines_app with "H"). rel_values.
  Qed.

  (** Associativity *)
  Lemma or_assoc_l (v1 v1' v2 v2' v3 v3' : val) A :
    (REL v1 << v1' : () → A) -∗
    (REL v2 << v2' : () → A) -∗
    (REL v3 << v3' : () → A) -∗
    REL or v1 (λ: <>, or v2 v3) << or (λ: <>, or v1' v2') v3' : A.
  Proof.
    iIntros "H1 H2 H3".
    rel_pure_l. (* TODO: should we write a value lambda instead? *)
    rel_pure_r.
    rel_apply_l or_refines_l.
    iSplit; last (rel_pure_l; rel_apply_l or_refines_l; iSplit).
    - rel_apply_r or_refines_r. iLeft. rel_pure_r.
      rel_apply_r or_refines_r. iLeft.
      iApply (refines_app with "H1"). rel_values.
    - rel_apply_r or_refines_r. iLeft. rel_pure_r.
      rel_apply_r or_refines_r. iRight.
      iApply (refines_app with "H2"). rel_values.
    - rel_apply_r or_refines_r. iRight.
      iApply (refines_app with "H3"). rel_values.
  Qed.

End rules.

(* TODO: write out the contextual refinements *)
