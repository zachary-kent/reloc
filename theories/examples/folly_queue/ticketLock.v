(* A ticket lock using a turn sequencer *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl cmra agree frac gset.
From reloc Require Import reloc.
From reloc.examples.folly_queue Require Import set turnSequencer.

Definition newlock : val := λ: <>,
  let: "turn" := ref #0 in
  let: "t" := newTS #() in
  ("t", "turn").
Definition acquire : val := rec: "acquire" "l" :=
  let: "t" := Fst "l" in
  let: "turn" := Snd "l" in
  let: "ct" := !"turn" in
  if: CAS "turn" "ct" ("ct" + #1)
  then waitForTurn "t" "ct";; "ct"
  else "acquire" "l".
Definition release : val := λ: "l" "ct",
  let: "t" := Fst "l" in
  completeTurn "t" "ct".

Section contents.
  Context `{!relocG Σ, !TSG Σ}.

  Context (N' : namespace).
  Context (R : iProp Σ).

  Definition N := N'.@"N".
  Definition LN := N'.@"ticketLock".

  Definition lock_inv_body (γTS : gname) turn : iProp Σ :=
    (∃ (n : nat), turn ↦ #n ∗ turns_from γTS n)%I.
  Definition lock_inv (γTS : gname) (ts : val) (turn : loc) : iProp Σ :=
    (isTS γTS (fun _ => R) ts ∗
           inv LN (lock_inv_body γTS turn))%I.
  Definition locked ts n := complete ts n.

  Lemma newlock_spec :
    {{{ R }}}
      newlock #()
    {{{ ts turn γTS, RET (ts, #turn); lock_inv γTS ts turn }}}.
  Proof.
    iIntros (Φ) "HR HΦ".
    unlock newlock. wp_rec.
    wp_alloc turn as "Hturn". wp_let.
    (* iMod (own_alloc ((● Excl' 0) ⋅ (◯ Excl' 0))) as (γ) "[Hγ HP]". *)
    (* { by apply auth_both_valid_discrete. } *)
    wp_bind (newTS #()).
    iApply (ts_mk_spec (fun _ => R)%I with "HR").
    iNext. iIntros (γTS ts) "[#Hts Hturns]".
    iMod (inv_alloc LN _ (lock_inv_body γTS turn) with "[Hturn Hturns]") as "#Hinv".
    { iNext. iExists 0. by iFrame. }
    wp_pures.
    iApply "HΦ". rewrite /lock_inv. by iFrame "Hts Hinv".
  Qed.

  Lemma turns_take γ m : turns_from γ m ⊢ turns_from γ (m + 1) ∗ turn γ m.
  Proof. by rewrite /turns_from /turn -own_op comm -take_first. Qed.

  Lemma acquire_spec γTS ts (turn : loc) :
    {{{ lock_inv γTS ts turn }}}
      acquire (ts, #turn)
    {{{ n, RET #n; locked ts n ∗ R }}}.
  Proof.
    iIntros (Φ) "#[Hts Hlinv] HΦ".
    wp_pures. iLöb as "IH". wp_rec. wp_pures.
    wp_bind (! #turn)%E.
    iInv LN as (n) "(Hturn & Htickets)" "Hcl".
    wp_load.
    iMod ("Hcl" with "[Hturn Htickets]") as "_".
    { iNext. iExists _; iFrame. }
    iModIntro. wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv LN as (n') "(Hturn & Htickets)" "Hcl".
    destruct (decide (n = n')); subst.
    - wp_cmpxchg_suc.
      rewrite turns_take. iDestruct "Htickets" as "[Htickets Hticket]".
      iMod ("Hcl" with "[Hturn Htickets]") as "_".
      { iNext. iExists _.
        rewrite -(Nat2Z.inj_add n' 1).
        assert (n' + 1 = S n') as -> by lia.
        by iFrame. }
      iModIntro. wp_pures.
      wp_apply (wait_spec with "[$Hts $Hticket]").
      iIntros "[HR Hcompl]". wp_pures. iApply "HΦ".
      by iFrame.
    - wp_cmpxchg_fail. naive_solver.
      iMod ("Hcl" with "[-HΦ]") as "_".
      { iNext. iExists _. by iFrame. }
      iModIntro. wp_pures.
      by iApply "IH".
  Qed.

  Lemma release_spec γTS ts (turn : loc) n :
    {{{ lock_inv γTS ts turn ∗ locked ts n ∗ R }}}
      release (ts, #turn) #n
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#[Hts Hlinv] [Hlk HR]] HΦ".
    wp_pures. wp_rec. wp_pures.
    by iApply (complete_spec with "[$Hts $Hlk $HR]").
  Qed.
End contents.
