From iris.algebra Require Import auth excl cmra agree frac gset.
From reloc Require Import reloc.
From reloc.lib Require Import lock.
From reloc.examples.folly_queue Require Import set.

(** * Implementation *)

Notation errorE := (#0 #1). (* This gets stuck *)

(* Turn Sequencer with simple spinning. Ignoring arithmetic, shifter turns and use of futex. *)

Definition newTS : val := λ: <>, ref #0.

Definition completeTurn : val :=
  rec: "complete" "state_" "turn" :=
    let: "state" := !"state_" in
    if: ("state" ≠ "turn")
    then errorE
    else "state_" <- ("turn" + #1).

Definition waitForTurn : val :=
  rec: "wait" "state_" "turn" :=
    let: "state" := !"state_" in
    if: ("state" = "turn") then #()
    else if: ("turn" < "state") then errorE
         else "wait" "state_" "turn".

Definition turnSequencer : val :=
  (newTS, completeTurn, waitForTurn).

Class TSG Σ := { TSG_tickets :> inG Σ (setUR nat) }.

(* Alternative spec for the TS. *)
Section spec.
  Context `{!relocG Σ, !TSG Σ}.

  Implicit Types R : nat → iProp Σ.

  Definition N : namespace := nroot .@ "TS".


  Definition turn γ n := own γ (set_singleton n).

  Definition turns_from γ n := own γ (set_above n).

  Definition turns γ n := own γ (set_upto n).

  Lemma turns_add γ m : turns γ m -∗ turn γ m -∗ turns γ (m + 1).
  Proof.
    iIntros "T S". iCombine "S T" as "T". by rewrite set_upto_singleton.
  Qed.

  Definition complete v (n : nat) : iProp Σ :=
    (∃ ℓ : loc, ⌜v = #ℓ⌝ ∗ ℓ ↦{#1/2} #n)%I.

  Definition TS_inv γ R ℓ : iProp Σ :=
    ∃ (n : nat), ℓ ↦{#1/2} #n ∗ turns γ n ∗ (R n ∗ complete #ℓ n ∨ turn γ n).

  Definition isTS (γ : gname) R v := (∃ ℓ : loc, ⌜v = #ℓ⌝ ∗ inv N (TS_inv γ R ℓ))%I.

  Lemma ts_mk_spec R :
   {{{ R 0 }}} newTS #() {{{ γ v, RET v; isTS γ R v ∗ turns_from γ 0 }}}.
  Proof.
    iIntros (ϕ) "Hr Hϕ".
    wp_rec.
    iApply wp_fupd.
    wp_alloc ℓ as "[ℓPts ℓPts']".
    iMod (own_alloc (set_above 0)) as (γ) "Hturns"; first done.
    iMod (own_unit (setUR nat)) as "H".
    iMod (inv_alloc N _ (TS_inv γ R ℓ)%I with "[-Hϕ Hturns] ") as "HI".
    { iNext. iExists 0. unfold turns.
      rewrite -set_upto_zero.
      iFrame "ℓPts H". iLeft. iFrame "Hr". iExists _; eauto with iFrame. }
    iApply "Hϕ".
    iModIntro. iFrame "Hturns". iExists _. iSplit; eauto with iFrame.
  Qed.

  Lemma wait_spec γ R v n :
   {{{ isTS γ R v ∗ turn γ n }}} waitForTurn v #n {{{ RET #(); R n ∗ complete v n }}}.
  Proof.
    iLöb as "IH".
    iIntros (ϕ) "[#Hts Ht] Hϕ".
    iDestruct "Hts" as (ℓ ->) "#Hinv".
    wp_rec.
    wp_pures.
    wp_bind (! _)%E.
    iInv N as (m) "(>ℓPts & Hturns & Hdisj)" "Hcl".
    wp_load.
    destruct (lt_eq_lt_dec n m) as [[Hle|<-]|Hho].
    - iDestruct (own_valid_2 with "Hturns Ht") as %HI%set_upto_singleton_valid.
      exfalso. lia.
    - iDestruct "Hdisj" as "[[Hr ℓPts'] | Ht']"; last first.
      { by iDestruct (own_valid_2 with "Ht Ht'") as %?%set_singleton_invalid. }
      iMod ("Hcl" with "[Ht ℓPts Hturns]") as "_".
      { iNext. iExists _. iFrame. }
      iModIntro. wp_pures.
      rewrite bool_decide_true //. wp_pures.
      iApply "Hϕ". by iFrame.
    - iMod ("Hcl" with "[-Hϕ Ht]") as "_".
      { iNext. iExists _. iFrame. }
      iModIntro. wp_pures.
      case_bool_decide; simplify_eq; first lia.
      wp_pures.
      rewrite bool_decide_false; last lia.
      wp_pures.
      iApply ("IH" with "[$Ht]"); last done.
      { iExists _. eauto with iFrame. }
  Qed.

  Lemma complete_spec γ R v n :
    {{{ isTS γ R v ∗ R (n + 1) ∗ complete v n }}} completeTurn v #n {{{ RET #(); True }}}.
  Proof.
    iIntros (ϕ) "(#Hts & Hr & Hc) Hϕ".
    wp_rec.
    wp_pures.
    wp_bind (! _)%E.
    iDestruct "Hts" as (ℓ ->) "#Hinv".
    iDestruct "Hc" as (ℓ1 ?) "Hc".
    simplify_eq/=.
    iInv N as (m) "(>ℓPts & >Hturns & [(_ & >Hc')|Ht])" "Hcl".
    { rewrite /complete.
      iDestruct "Hc'" as (ℓ1' ?) "Hc'".
      simplify_eq/=.
      iCombine "ℓPts Hc'" as "ℓPts".
      iDestruct (mapsto_valid_2 with "ℓPts Hc") as %[?%Qp_not_add_le_l _].
      done. }
    wp_load.
    iDestruct (mapsto_agree with "ℓPts Hc") as %[= Heq].
    iMod ("Hcl" with "[Ht ℓPts Hturns]") as "_".
    { iNext. iExists m. iFrame. }
    iModIntro. wp_pures. simplify_eq/=.
    rewrite bool_decide_true //.
    wp_pures.
    iInv N as (m) "(>ℓPts & >Hturns & [(_ & >Hc')|>Ht])" "Hcl".
    { rewrite /complete.
      iDestruct "Hc'" as (ℓ1' ?) "Hc'".
      simplify_eq/=.
      iCombine "ℓPts Hc'" as "ℓPts".
      iDestruct (mapsto_valid_2 with "ℓPts Hc") as %[?%Qp_not_add_le_l _].
      done. }
    iDestruct (mapsto_combine with "ℓPts Hc") as "[ℓPts %Heq]".
    simplify_eq/=.
    rewrite dfrac_op_own Qp_half_half.
    wp_store.
    assert ((n + 1)%Z = (n + 1)%nat) as ->. { lia. }
    iDestruct "ℓPts" as "[ℓPts ℓPts']".
    iDestruct (turns_add with "Hturns Ht") as "Hturns".
    iMod ("Hcl" with "[-Hϕ]") as "_".
    { iNext. iExists (n + 1). iFrame. iLeft. iFrame. iExists _; eauto with iFrame. }
    iModIntro. by iApply "Hϕ".
  Qed.

End spec.
