From iris.proofmode Require Import tactics.
From reloc Require Import reloc.
Set Default Proof Using "Type".

(* TODO: these modules should be values -- but we don't have refines_pair for values *)
Definition bit_bool : expr :=
  (#true, (λ: "b", ~ "b"), (λ: "b", "b")).

Definition flip_nat : val := λ: "n",
  if: "n" = #0
  then #1
  else #0.
Definition bit_nat : expr :=
  (#1, flip_nat, (λ: "b", "b" = #1)).

Definition bitτ : type :=
  (TExists (TProd (TProd (TVar 0)
                         (TArrow (TVar 0) (TVar 0)))
                         (TArrow (TVar 0) (TBool))))%nat.


Section bit_refinement.
  Context `{relocG Σ}.

  Definition bitf (b : bool) : nat :=
    match b with
    | true => 1
    | false => 0
    end.

  (* This is the graph of the `bitf` function *)
  Definition bitτi : lrel Σ := LRel (λ v1 v2,
    (∃ b : bool, ⌜v1 = #b⌝ ∗ ⌜v2 = #(bitf b)⌝))%I.

  Lemma bit_refinement Δ :
    REL bit_bool << bit_nat : (interp bitτ Δ).
  Proof.
    unfold bit_bool, bit_nat.
    unfold bitτ. simpl.
    iApply (refines_exists bitτi).
    progress repeat iApply refines_pair.
    - rel_values.
    - unfold flip_nat. rel_pure_l.
      iApply refines_arrow_val.
      iIntros "!#" (v1 v2) "/=".
      iIntros ([b [? ?]]); simplify_eq/=.
      repeat rel_pure_l. repeat rel_pure_r.
      destruct b; simpl; rel_if_r; rel_values.
    - rel_pure_l. rel_pure_r.
      iApply refines_arrow_val.
      iIntros "!#" (v1 v2) "/=".
      iIntros ([b [? ?]]); simplify_eq/=.
      repeat rel_pure_l. repeat rel_pure_r.
      destruct b; simpl; rel_values.
  Qed.

End bit_refinement.

Theorem bit_ctx_refinement :
  ∅ ⊨ bit_bool ≤ctx≤ bit_nat : bitτ.
Proof.
  eapply (refines_sound relocΣ).
  iIntros (? Δ). iApply (bit_refinement Δ).
Qed.
