From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth gset.
From reloc Require Import reloc.
From reloc.prelude Require Export arith.
From reloc.examples.folly_queue Require Export set turnSequencer.

Definition enqueueWithTicket : val := λ: "this" "ticket" "v",
  let: "t" := Fst "this" in
  let: "r" := Snd "this" in
  let: "turn" := "ticket" * #2 in
  waitForTurn "t" "turn";;
  "r" <- SOME "v";;
  completeTurn "t" "turn".

Definition getSome : val := λ: "r",
  match: !"r" with
    NONE => errorE (* Error *)
  | SOME "x" => "r" <- NONE;; "x"
  end.

Definition dequeueWithTicket : val := λ: "this" "ticket",
  let: "t" := Fst "this" in
  let: "r" := Snd "this" in
  let: "turn" := ("ticket" * #2) + #1 in
  waitForTurn "t" "turn";;
  let: "v" := getSome "r" in
  completeTurn "t" "turn";;
  "v".

(* The single-element queue used by the MPMC queue. *)
Definition newSEQ : val := λ: <>,
  let: "r" := ref NONE in
  let: "t" := newTS #() in
  ("t", "r").

(* Code for a single element queue that manages tickets itself. *)
Definition enqueue : val := rec: "enqueue" "t" "r" "ticket_" "v" :=
  let: "ticket" := FAA "ticket_" #1 in
  enqueueWithTicket ("t", "r") "ticket" "v".

Definition dequeue : val := rec: "dequeue" "t" "r" "ticket_" <> :=
  let: "ticket" := FAA "ticket_" #1 in
  dequeueWithTicket ("t","r") "ticket".

Definition newQueue : val := λ: <>,
  let: "popTicket" := ref #0 in
  let: "pushTicket" := ref #0 in
  let: "r" := ref NONE in
  let: "t" := newTS #() in
  (λ: "v", enqueue "t" "r" "pushTicket" "v", λ: <>, dequeue "t" "r" "popTicket" #()).

(* Alternative spec for the TS. *)
Section spec.
  Context `{!relocG Σ, !TSG Σ}.

  Definition Nseq : namespace := nroot .@ "SEQ".

  (* R is the resource that the single element queue protects. The i'th dequeue
     is sure to get a value, v, that satisfies R i v. *)
  Implicit Type R : nat → val → iProp Σ.

  (* The resource for the turn sequencer. *)
  Definition TSR R (ℓ : loc) (n : nat) : iProp Σ :=
    (if even n
     then ℓ ↦ NONEV
     else ∃ v, ℓ ↦ SOMEV v ∗ R ((n - 1) / 2) v)%I.

  Definition isSEQ (γ : gname) R (v : val) : iProp Σ :=
    ∃ ts (ℓ : loc), ⌜v = (ts, #ℓ)%V⌝ ∗ isTS γ (TSR R ℓ) ts.

  Definition enqueue_turns γ n := own γ (set_even_drop n).
  Definition dequeue_turns γ n := own γ (set_odd_drop n).
  Definition enqueue_turn γ n := own γ (set_singleton (2 * n)).
  Definition dequeue_turn γ n := own γ (set_singleton (2 * n + 1)).

  Lemma enqueue_turns_take γ n :
    enqueue_turns γ n ⊣⊢ enqueue_turns γ (n + 1) ∗ enqueue_turn γ n.
  Proof. by rewrite -own_op -set_even_drop_singleton. Qed.

  Lemma dequeue_turns_take γ n :
    dequeue_turns γ n ⊣⊢ dequeue_turns γ (n + 1) ∗ dequeue_turn γ n.
  Proof. by rewrite -own_op -set_odd_drop_singleton. Qed.

  Lemma newSEQ_spec (v : val) R :
    {{{ True }}} newSEQ v {{{ γ v, RET v; isSEQ γ R v ∗ enqueue_turns γ 0 ∗ dequeue_turns γ 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.
    wp_alloc ℓ as "pts". wp_pures.
    wp_apply (ts_mk_spec (TSR R ℓ) with "pts").
    iIntros (γ ts) "[Hts turns]".
    wp_pures.
    iApply ("HΦ" $! γ).
    iSplitL "Hts". { iExists _, _. iFrame. done. }
    rewrite /turns_from /enqueue_turns /dequeue_turns.
    rewrite set_above_zero.
    rewrite split_even_odd.
    rewrite set_even_drop_zero.
    rewrite set_odd_drop_zero.
    rewrite own_op.
    by iFrame.
  Qed.

  (* For the [lia] tactic. *)
  (* To support Z.div, Z.modulo, Z.quot, and Z.rem: *)
  Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

  Lemma enqueueWithTicket_spec' γ R v x n :
  {{{ isSEQ γ R v ∗ enqueue_turn γ n ∗ R n x }}}
    enqueueWithTicket v #n x
  {{{ RET #(); True }}}.
  Proof. 
    iIntros (Φ) "(isSEQ & Hturn & HR) HΦ".
    iDestruct "isSEQ" as (ts ℓ) "[-> #Hts]".
    wp_rec.
    wp_pures.
    assert ((n * 2)%Z = (2 * n)%nat) as ->. { lia. }
    wp_apply (wait_spec with "[$Hts Hturn]"); first done.
    iIntros "[Htsr Hclose]".
    iEval (rewrite /TSR) in "Htsr".
    wp_pures.
    assert (Nat.even (2 * n) = true) as ->.
    { apply Nat.even_spec, Even_mul2. }
    wp_store.
    wp_apply (complete_spec with "[Hclose HR Htsr]").
    { simpl. iFrame "#∗".
      rewrite /TSR.
      assert (Nat.even (n + (n + 0) + 1) = false) as ->.
      { replace (n + (n + 0) + 1) with (S (2 * n)) by lia.
        rewrite Nat.even_succ. rewrite -Nat.negb_even.
        assert (Nat.even (2 * n) = true) as ->; last done.
        apply Nat.even_spec. apply Even_mul2. }
      iExists _. iFrame.
      replace (n + (n + 0) + 1 - 1) with (n * 2) by lia.
      rewrite Nat.div_mul; last done.
      done. }
    iAssumption.
  Qed.
 
  Lemma dequeueWithTicket_spec' γ R v n :
  {{{ isSEQ γ R v ∗ dequeue_turn γ n }}}
    dequeueWithTicket v #n
  {{{ v, RET v; R n v }}}.
  Proof.
    iIntros (Φ) "(isSEQ & Hturn) HΦ".
    iDestruct "isSEQ" as (ts ℓ) "[-> #Hts]".
    wp_rec. wp_pures.
    assert ((n * 2 + 1)%Z = (2 * n + 1)%nat) as -> by lia.
    wp_apply (wait_spec with "[$Hts Hturn]"); first done.
    iIntros "[Htsr Hclose]".
    rewrite /getSome. wp_pures.
    iEval (rewrite /TSR) in "Htsr".
    rewrite Nat.add_0_r.
    assert (Nat.even (2 * n + 1) = false) as ->.
    { replace (2 * n + 1) with (S (2 * n)) by lia.
      rewrite Nat.even_succ. rewrite -Nat.negb_even.
      assert (Nat.even (2 * n) = true) as ->; last done.
      apply Nat.even_spec. apply Even_mul2. }
    iDestruct "Htsr" as (v) "[pts HR]".
    wp_load.
    wp_store. wp_pures.
    wp_apply (complete_spec with "[Hclose pts]").
    { iFrame "#∗".
      replace (n + n + 1 + 1) with (2 * (n + 1)) by lia.
      replace (n + n + 1) with (2 * n + 1) by lia.
      rewrite /TSR.
      assert (Nat.even _ = true) as ->.
      { apply Nat.even_spec. apply Even_mul2. }
      by iFrame. }
    iIntros "_".
    wp_pures.
    iApply "HΦ".
    replace (2 * n + 1 - 1) with (n * 2) by lia.
    rewrite Nat.div_mul; last done.
    by iFrame.
  Qed.

  Lemma dequeueWithTicket_spec2 (γ : gname) R (v : val) (n : nat) (Φ : val → iPropI Σ) :
    isSEQ γ R v ∗ dequeue_turn γ n
    -∗ ▷ (∀ v0 : val, R n v0 ={⊤}=∗ ▷ Φ v0 )
      -∗ WP dequeueWithTicket v #n {{ v, Φ v }}.
  Proof.
    iIntros "(isSEQ & Hturn) HΦ".
    iDestruct "isSEQ" as (ts ℓ) "[-> #Hts]".
    wp_rec. wp_pures.
    assert ((n * 2 + 1)%Z = (2 * n + 1)%nat) as -> by lia.
    wp_apply (wait_spec with "[$Hts Hturn]"); first done.
    iIntros "[Htsr Hclose]".
    rewrite /getSome. wp_pures.
    iEval (rewrite /TSR) in "Htsr".
    rewrite Nat.add_0_r.
    assert (Nat.even (2 * n + 1) = false) as ->.
    { replace (2 * n + 1) with (S (2 * n)) by lia.
      rewrite Nat.even_succ. rewrite -Nat.negb_even.
      assert (Nat.even (2 * n) = true) as ->; last done.
      apply Nat.even_spec. apply Even_mul2. }
    iDestruct "Htsr" as (v) "[pts HR]".
    wp_load.
    wp_store. wp_pures.
    wp_apply (complete_spec with "[Hclose pts]").
    { iFrame "#∗".
      replace (n + n + 1 + 1) with (2 * (n + 1)) by lia.
      replace (n + n + 1) with (2 * n + 1) by lia.
      rewrite /TSR.
      assert (Nat.even _ = true) as ->.
      { apply Nat.even_spec. apply Even_mul2. }
      by iFrame. }
    iIntros "_".
    replace (2 * n + 1 - 1) with (n * 2) by lia.
    rewrite Nat.div_mul; last done.
    iMod ("HΦ" $! v with "HR") as "HI".
    wp_pures.
    by iFrame.
  Qed.

End spec.
