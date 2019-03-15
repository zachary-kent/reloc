From reloc Require Import reloc.
From iris.heap_lang.lib Require Export assert.
Set Default Proof Using "Type".

Definition assert : val :=
  λ: "v", if: "v" #() then #() else #0 #0. (* #0 #0 is unsafe *)
(* just below ;; *)
Notation "'assert:' e" := (assert (λ: <>, e))%E (at level 99) : expr_scope.

(* Nested relational specifications *)
Lemma rel_assert_l `{!relocG Σ} K e t A :
  (∀ K t A, (REL fill K (of_val #true) << t : A) -∗ REL fill K e << t : A) -∗
  (▷ REL fill K (of_val #()) << t : A) -∗
  REL fill K (assert: e)%V << t : A.
Proof.
  iIntros "H1 H2". rel_rec_l. rel_rec_l.
  rel_apply_l "H1". by rel_if_l.
Qed.
