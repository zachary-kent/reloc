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

Notation "e1 ⊕ e2" := (or (λ: <>, e1)%E (λ: <>, e2)%E)
                        (at level 60) : expr_scope.
Notation "e1 ⊕ e2" := (or (λ: <>, e1)%V (λ: <>, e2)%V)
                        (at level 60) : val_scope.

Section rules.
  Context `{relocG Σ}.

  (** Symbolic execution rule for the LHS *)
  Definition or_inv x : iProp Σ :=
    (x ↦ #0 ∨ x ↦ #1)%I.
  Definition orN := nroot .@ "orN".
  Ltac close_inv := iNext; (iLeft + iRight); by iFrame.

  Lemma or_refines_l K (e1 e2 : expr) t A :
    ((REL fill K e1 << t : A)
     ∧ (REL fill K e2 << t : A)) -∗
    REL fill K (e1 ⊕ e2)%V << t : A.
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
  Lemma or_refines_r K (e1 e2 : expr) e A :
    ((REL e << fill K e1 : A)
     ∨ (REL e << fill K e2 : A)) -∗
    REL e << fill K (e1 ⊕ e2)%V : A.
  Proof.
    iIntros "H".
    rel_rec_r. repeat rel_pure_r.
    rel_alloc_r x as "Hx".
    repeat rel_pure_r.
    rel_fork_r j as "Hj".
    repeat rel_pure_r.
    iDestruct "H" as "[H | H]".
    - rel_load_r. repeat rel_pure_r. eauto with iFrame.
    - tp_store j.
      rel_load_r. repeat rel_pure_r. eauto with iFrame.
  Qed.

  Opaque or.

  (** Compatibility rule *)
  Lemma or_compatible e1 e2 e1' e2' A :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : A) -∗
    REL (e1 ⊕ e2)%V << (e1' ⊕ e2')%V : A.
  Proof.
    iIntros "H1 H2".
    rel_apply_l or_refines_l. iSplit.
    - rel_apply_r or_refines_r. eauto with iFrame.
    - rel_apply_r or_refines_r. eauto with iFrame.
  Qed.

  (** Choice on the RHS *)
  Lemma or_choice_1_r (e1 e1' e2 : val) A :
    (REL e1 << e1' : A) -∗
    REL e1 << (e1' ⊕ e2)%V : A. (* TODO: in the value scope *)
  Proof.
    iIntros "H".
    rel_apply_r or_refines_r. iLeft. eauto.
  Qed.

  (** Idempotence *)
  Lemma or_idemp_r (e e' : expr) A :
    (REL e << e' : A) -∗
    REL e << (e' ⊕ e')%V : A.
  Proof.
    iIntros "H".
    rel_apply_r or_refines_r. by iLeft.
  Qed.

  Lemma or_idemp_l (e e' : expr) A :
    (REL e << e' : A) -∗
    REL (e ⊕ e)%V << e' : A.
  Proof.
    iIntros "H".
    rel_apply_l or_refines_l.
    iSplit; eauto.
  Qed.

  (** Commutativity *)
  Lemma or_comm e1 e2 e1' e2' A :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : A) -∗
    REL (e1 ⊕ e2)%V << (e2' ⊕ e1')%V : A.
  Proof.
    iIntros "H1 H2".
    rel_apply_l or_refines_l. iSplit.
    - rel_apply_r or_refines_r. by iRight.
    - rel_apply_r or_refines_r. by iLeft.
  Qed.

  (** Bottom is the unit *)
  Lemma or_bot_l e e' A :
    (REL e << e' : A) -∗
    REL (e ⊕ bot #())%V << e' : A.
  Proof.
    iIntros "H".
    rel_apply_l or_refines_l. iSplit; first done.
    rel_apply_l bot_l.
  Qed.

  Lemma or_bot_r e e' A :
    (REL e << e' : A) -∗
    REL e << (e' ⊕ bot #())%V : A.
  Proof.
    iIntros "H".
    rel_apply_r or_refines_r. by iLeft.
  Qed.

  (** Associativity *)
  Lemma or_assoc_l e1 e2 e3 e1' e2' e3' A :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : A) -∗
    (REL e3 << e3' : A) -∗
    REL (e1 ⊕ (e2 ⊕ e3)%V)%V << ((e1' ⊕ e2')%V ⊕ e3')%V : A.
  Proof.
    iIntros "H1 H2 H3".
    repeat (rel_apply_l or_refines_l; iSplit).
    - rel_apply_r or_refines_r. iLeft.
      rel_apply_r or_refines_r. by iLeft.
    - rel_apply_r or_refines_r. iLeft.
      rel_apply_r or_refines_r. by iRight.
    - rel_apply_r or_refines_r. by iRight.
  Qed.

  (** Interaction between OR and sequencing. *)
  (** Standard in algebraic models of programming. *)
  Lemma or_seq_1 (f g h f' g' h' : expr) A :
    (REL f << f' : A) -∗
    (REL g << g' : A) -∗
    (REL h << h' : A) -∗
    REL ((f ⊕ g)%V;; h)
      << ((f';; h') ⊕ (g';; h'))%V : A.
  Proof.
    iIntros "Hf Hg Hh".
    rel_apply_l or_refines_l; iSplit; simpl.
    - rel_apply_r or_refines_r.
      iLeft. iApply (refines_seq with "Hf Hh").
    - rel_apply_r or_refines_r.
      iRight. iApply (refines_seq with "Hg Hh").
  Qed.
  Lemma or_seq_2 (f g h f' g' h' : expr) A :
    (REL f << f' : A) -∗
    (REL g << g' : A) -∗
    (REL h << h' : A) -∗
    REL ((f;; h) ⊕ (g;; h))%V
      << ((f' ⊕ g')%V;; h') : A.
  Proof.
    iIntros "Hf Hg Hh".
    rel_apply_l or_refines_l; iSplit; simpl.
    - rel_apply_r or_refines_r.
      iLeft. iApply (refines_seq with "Hf Hh").
    - rel_apply_r or_refines_r.
      iRight. iApply (refines_seq with "Hg Hh").
  Qed.

  (** This is less standard: it holds in Kleene Algebras, but usually
  this is not required in process algebras, because the terms are
  _not_ bisimular *)
  Lemma seq_or_1 (f g h f' g' h' : expr) A :
    (REL f << f' : A) -∗
    (REL g << g' : A) -∗
    (REL h << h' : A) -∗
    REL ((f;; g) ⊕ (f;; h))%V
      << (f';; (g' ⊕ h')%V) : A.
  Proof.
    iIntros "Hf Hg Hh".
    rel_apply_l or_refines_l. iSplit.
    - iApply (refines_seq with "Hf").
      rel_apply_r or_refines_r. by iLeft.
    - iApply (refines_seq with "Hf").
      rel_apply_r or_refines_r. by iRight.
  Qed.


  (** To prove the refinement in the other direction, we instrument
  our program with prophecies and resolve them when we actually make
  the choice on the LHS *)
  Definition to_choice (vs : list val) : bool :=
    match vs with
    | LitV (LitInt 0)::_ => true
    | _ => false
    end.

  Lemma seq_or_2' (f g h f' g' h' : expr) A :
    is_closed_expr [] f →
    is_closed_expr [] g →
    is_closed_expr [] h →
    (REL f << f' : A) -∗
    (REL g << g' : A) -∗
    (REL h << h' : A) -∗
    REL (let: "p" := NewProph in
         f;;
         (((resolve_proph: "p" to: #0);; g) ⊕
          ((resolve_proph: "p" to: #1);; h))%E) << (* Here we *have to* use the expr scope, otherwise "p" won't be substituted *)
      ((f';; g') ⊕ (f';; h'))%V : A.
  Proof.
    iIntros (???) "Hf Hg Hh".
    rel_newproph_l vs p as "Hp". repeat rel_pure_l.
    (rewrite !(subst_is_closed []) //; try by set_solver); [].
    rel_apply_r or_refines_r.
    destruct (to_choice vs) as [|] eqn:Hchoice.
    - iLeft. iApply (refines_seq with "Hf").
      repeat rel_pure_l.
      rel_apply_l or_refines_l. iSplit.
      + rel_apply_l refines_resolveproph_l. iModIntro. iExists _; iFrame.
        iNext. iIntros (vs' ->) "Hp". repeat rel_pure_l. done.
      + rel_apply_l refines_resolveproph_l. iModIntro. iExists _; iFrame.
        iNext. iIntros (vs' ->) "Hp".
        simpl in Hchoice. inversion Hchoice.
    - iRight. iApply (refines_seq with "Hf").
      repeat rel_pure_l.
      rel_apply_l or_refines_l. iSplit; last first.
      + rel_apply_l refines_resolveproph_l. iModIntro. iExists _; iFrame.
        iNext. iIntros (vs' ->) "Hp". repeat rel_pure_l. done.
      + rel_apply_l refines_resolveproph_l. iModIntro. iExists _; iFrame.
        iNext. iIntros (vs' ->) "Hp".
        simpl in Hchoice. inversion Hchoice.
  Qed.

  (** We then prove that the non-instrumented program refines the original one *)
  Lemma seq_or_2_instrument (f g h f' g' h' : expr) A :
    is_closed_expr [] f' →
    is_closed_expr [] g' →
    is_closed_expr [] h' →
    (REL f << f' : A) -∗
    (REL g << g' : A) -∗
    (REL h << h' : A) -∗
    REL (f;; (g ⊕ h)%V) <<
    (let: "p" := NewProph in
         f';;
         (((resolve_proph: "p" to: #0);; g') ⊕
          ((resolve_proph: "p" to: #1);; h'))%E) : A.
  Proof.
    iIntros (???) "Hf Hg Hh".
    rel_newproph_r p. repeat rel_pure_r.
    (rewrite !(subst_is_closed []) //; try by set_solver); [].
    iApply (refines_seq with "Hf").
    repeat rel_pure_r. iApply (or_compatible with "[Hg] [Hh]").
    - rel_resolveproph_r. by repeat rel_pure_r.
    - rel_resolveproph_r. by repeat rel_pure_r.
  Qed.

End rules.

(* TODO: write out the contextual refinements *)
