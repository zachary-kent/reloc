(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Semantic typeability and equivalences for fixed point combinators. *)
From iris.proofmode Require Import tactics.
From reloc Require Export proofmode.

Definition bot : val := rec: "bot" <> := "bot" #().

(** Standard Y combinator *)
Definition Y : val :=
  λ: "f", (λ: "x", "f" ("x" "x")) (λ: "x", "f" ("x" "x")).

(** Landin's knot: recursion through state *)
Definition Knot : val := λ: "f",
  let: "z" := ref bot
  in "z" <- (λ: "x", "f" (!"z" #()));; !"z" #().

(** We also support recursion in the language natively! *)
Definition F : val := rec: "f" "g" :=
  "g" ("f" "g").

Section contents.
  Context `{relocG Σ}.

  Lemma bot_l K t A :
    REL fill K (bot #()) << t : A.
  Proof.
    iLöb as "IH".
    rel_rec_l.
    iApply "IH".
  Qed.

  Lemma Y_semtype A :
    REL Y << Y : (A → A) → A.
  Proof.
    unlock Y.
    iApply refines_arrow.
    iAlways. iIntros (f1 f2) "#Hff".
    rel_let_l. rel_let_r.
    rel_pure_l. rel_pure_r.
    rel_pure_l. rel_pure_r.
    iLöb as "IH".
    rel_pure_l. rel_pure_r.
    iApply (refines_app with "Hff").
    by iApply "IH".
  Qed.

  Lemma FIX_semtype A :
    REL F << F : (A → A) → A.
  Proof.
    unlock F.
    iApply refines_arrow.
    iAlways. iIntros (f1 f2) "#Hff".
    iLöb as "IH".
    rel_let_l. rel_let_r.
    iApply (refines_app with "Hff").
    by iApply "IH".
  Qed.

  (** Landin's knot is equivalent to the Y combinator *)
  Lemma KNOT_Y A :
    REL Knot << Y : (A → A) → A.
  Proof.
    unlock Y Knot.
    iApply refines_arrow.
    iAlways. iIntros (f1 f2) "#Hff".
    rel_let_l. rel_let_r.
    rel_pure_r. rel_pure_r.
    rel_alloc_l z as "Hz". repeat rel_pure_l.
    rel_store_l. repeat rel_pure_l.
    iLöb as "IH".
    rel_let_r.
    rel_load_l. rel_let_l.
    iApply (refines_app with "Hff").
    by iApply "IH".
  Qed.

  Lemma Y_KNOT A :
    REL Y << Knot : (A → A) → A.
  Proof.
    unlock Y Knot.
    iApply refines_arrow.
    iAlways. iIntros (f1 f2) "#Hff".
    rel_let_l. rel_let_r.
    rel_pure_l. rel_pure_l.
    rel_alloc_r z as "Hz". repeat rel_pure_r.
    rel_store_r. repeat rel_pure_r.
    iLöb as "IH".
    rel_let_l.
    rel_load_r. rel_let_r.
    iApply (refines_app with "Hff").
    by iApply "IH".
  Qed.

  (** Native recursion is equivalent to the Y-combinator *)
  Lemma FIX_Y A :
    REL F << Y : (A → A) → A.
  Proof.
    unlock Y F.
    iApply refines_arrow.
    iAlways. iIntros (f1 f2) "#Hff".
    rel_pure_r. rel_pure_r. rel_pure_r.
    iLöb as "IH".
    rel_let_l. rel_let_r.
    iApply (refines_app with "Hff").
    by iApply "IH".
  Qed.

  Lemma Y_FIX A :
    REL Y << F : (A → A) → A.
  Proof.
    unlock Y F.
    iApply refines_arrow.
    iAlways. iIntros (f1 f2) "#Hff".
    rel_pure_l. rel_pure_l. rel_pure_l.
    iLöb as "IH".
    rel_let_l. rel_let_r.
    iApply (refines_app with "Hff").
    by iApply "IH".
  Qed.

  (** Native recursion is prefixpoint in the ctx refinement theory *)
  (* Note that we only have this for values - this does not hold for arbitrary stateful computations *)
  Lemma FIX_prefixpoint α β (v : val) :
    □ (REL v << v : ((α → β) → α → β)) -∗
    REL v (F v) << F v : (α → β).
  Proof.
    iIntros "#Hv".
    rel_rec_r.
    iApply (refines_app with "Hv").
    iApply (refines_app with "[] Hv").
    iApply FIX_semtype.
  Qed.

  (** Same but as a post-fixed point *)
  Lemma FIX_postfixpoint α β (v : val) :
    □ (REL v << v : ((α → β) → α → β)) -∗
    REL F v << v (F v) : (α → β).
  Proof.
    iIntros "#Hv".
    rel_rec_l.
    iApply (refines_app with "Hv").
    iApply (refines_app with "[] Hv").
    iApply FIX_semtype.
  Qed.

  (** Open Question: show that F is also the greatest fixed point *)
End contents.
