From iris.proofmode Require Import tactics.
From reloc Require Import proofmode.
From reloc.typing Require Import types interp fundamental.
From reloc.typing Require Import soundness.

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
  Definition bitτi : lty2 Σ := Lty2 (λ v1 v2,
    (∃ b : bool, ⌜v1 = #b⌝ ∗ ⌜v2 = #(bitf b)⌝))%I.

  Lemma bit_refinement Δ :
    REL bit_bool << bit_nat : (interp bitτ Δ).
  Proof.
    unfold bit_bool, bit_nat.
    unfold bitτ. simpl.
    iApply (refines_exists bitτi).
    progress repeat iApply refines_pair.
    - rel_values.
    - unfold flip_nat. rel_pure_l. unlock. (* TODO: can we make the tactics do unlocking? *)
      iApply refines_arrow_val.
      iIntros "!#" (v1 v2) "/=".
      iIntros ([b [? ?]]); simplify_eq/=.
      repeat rel_pure_l. repeat rel_pure_r.
      destruct b; simpl; rel_if_r; rel_values.
    - rel_pure_l. rel_pure_r. unlock.
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
  eapply (logrel_ctxequiv relocΣ).
  iIntros (? ? vs) "Hvs". simpl.
  (* TODO: this is not the place to have this boilerplate *)
  rewrite !lookup_delete.
  iApply (bit_refinement Δ).
Qed.

(* Definition heapify : val := λ: "b", Unpack "b" $ λ: "b'", *)
(*   let: "init" := Fst (Fst "b'") in *)
(*   let: "flip" := Snd (Fst "b'") in *)
(*   let: "view" := Snd "b'" in *)
(*   let: "x" := ref "init" in *)
(*   let: "l" := newlock #() in *)
(*   let: "flip_ref" := λ: <>, acquire "l";; "x" <- "flip" (!"x");; release "l" in *)
(*   let: "view_ref" := λ: <>, "view" (!"x") in *)
(*   (#(), "flip_ref", "view_ref"). *)

(* Lemma heapify_type Γ : *)
(*   typed Γ heapify (TArrow bitτ bitτ). *)
(* Proof. *)
(*   unfold bitτ. unfold heapify. *)
(*   unlock. *)
(*   repeat (econstructor; solve_typed). (* TODO: solve_typed does not work by itself :( *) *)
(* Qed. *)
(* Hint Resolve heapify_type : typeable. *)
