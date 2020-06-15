(* ReLoC -- Relational logic for fine-grained concurrency *)
(** A simple bit module *)
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

Definition bitτ : type := ∃: #0 * (#0 → #0) * (#0 → TBool).

Section bit_refinement.
  Context `{!relocG Σ}.

  Definition R : lrel Σ :=
    LRel (λ v1 v2, (⌜v1 = #true⌝ ∧ ⌜v2 = #1⌝) ∨ (⌜v1 = #false⌝ ∧ ⌜v2 = #0⌝))%I.

  Lemma bit_refinement Δ : ⊢ REL bit_bool << bit_nat : interp bitτ Δ.
  Proof.
    unfold bitτ; simpl.
    iApply (refines_pack R).
    progress repeat iApply refines_pair.
    - rel_values.
    - unfold flip_nat. rel_pure_l.
      iApply refines_arrow_val.
      iIntros "!#" (v1 v2) "/=".
      iIntros ([[-> ->] | [-> ->]]);
        rel_pures_l; rel_pures_r; rel_values.
    - rel_pure_l. rel_pure_r.
      iApply refines_arrow_val.
      iIntros "!#" (v1 v2) "/=".
      iIntros ([[-> ->] | [-> ->]]);
        rel_pures_l; rel_pures_r; rel_values.
  Qed.

End bit_refinement.

Theorem bit_ctx_refinement :
  ∅ ⊨ bit_bool ≤ctx≤ bit_nat : bitτ.
Proof. auto using (refines_sound relocΣ), bit_refinement. Qed.
