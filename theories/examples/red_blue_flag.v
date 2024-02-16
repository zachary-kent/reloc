(* This example considers two implementations of a concurrent flag. That is, a
   single "bit" with a flip operation and a read operation.

   The example demonstrates how to handle an _external_ linearization points in
   ReLoC.

   The specification uses a lock to guard the critical section in flip.

   This example is from "Logical Relations for Fine-Grained Concurrency". *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl cmra agree frac gset csum.
From reloc Require Import reloc lib.lock.

(* blueFlag - the specification *)

Definition blueFlip : val := λ: "flag" "lock",
  acquire "lock" ;;
  "flag" <- ~ !"flag" ;;
  release "lock".

Definition blueRead : val := λ: "flag", !"flag".

Definition blueFlag : val :=  λ: <>,
  let: "flag" := ref #true in
  let: "lock" := newlock #() in
  (λ: <>, blueRead "flag",
   λ: <>, blueFlip "flag" "lock").

(* redFlag - the implementation *)

(* The value of the side channel represents:
   0 - No one is using the side channel.
   1 - An offer is made on the side channel.
   2 - An offer was accepted. *)

Definition redFlip : val := λ: "flag" "chan",
  rec: "try" <> :=
    if: CAS "chan" #1 #2 then #() else (* Take an offer. *)
    if: CAS "flag" #true #false then #() else (* LP if this succeeds. *)
    if: CAS "flag" #false #true then #() else (* LP if this succeeds. *)
    if: CAS "chan" #0 #1 (* Make an offer. This is _not_ LP but when someone takes the offer our LP is during the execution of "someone". *)
    then (if: CAS "chan" #1 #0 then "try" #() else "chan" <- #0;; #()) (* Did someone take our offer? *)
    else "try" #().

Definition redRead : val :=
  λ: "flag" <>, ! "flag".

Definition redFlag : val :=  λ: <>,
  let: "flag" := ref #true in
  let: "chan" := ref #0 in
  (redRead "flag", redFlip "flag" "chan").


Definition offer : Type := Qp * gname * (list ectx_item).
Definition offerR :=
  csumR (exclR unitR)
        (prodR fracR (agreeR ref_idO)).

Class offerPreG Σ := OfferPreG {
  offer_inG :: inG Σ offerR;
  offer_token_inG :: inG Σ fracR;
}.

Section offer_theory.
  Context `{!relocG Σ, !lockG Σ, !offerPreG Σ}.

  Definition no_offer γ := own γ (Cinl (Excl ())).

  Definition offer_elm (q : Qp) k : offerR := Cinr (q, to_agree k).

  Definition own_offer γ q k := own γ (offer_elm q k).

  Definition half_offer γ k := own_offer γ (1/2) k.

  Definition quarter_offer γ k := own_offer γ (1/4) k.

  (* Global Instance no_offer_exclusive' : Exclusive (Cinl (Excl ()) : offerR).
  Proof. apply _. Qed.  *)

  Lemma no_offer_alloc : ⊢ |==> ∃ γ, no_offer γ.
  Proof. by iApply own_alloc. Qed.

  Lemma own_offer_valid γ q k : (own_offer γ q k -∗ ⌜(q ≤ 1)%Qp⌝).
  Proof.
    iIntros "Hown".
    rewrite /own_offer /offer_elm.
    iDestruct (own_valid with "Hown") as %[Hown _].
    done.
  Qed.

  Lemma no_offer_exclusive γ q k : no_offer γ -∗ own_offer γ q k -∗ False.
  Proof. iIntros "O P". by iCombine "O P" gives %?. Qed.

  Lemma no_offer_to_offer γ k : no_offer γ ==∗ own_offer γ 1 k.
  Proof.
    iIntros "O".
    iMod (own_update with "O") as "$"; last done.
    by apply cmra_update_exclusive.
  Qed.

  Lemma offer_to_no_offer γ k : own_offer γ 1 k ==∗ no_offer γ.
  Proof.
    iIntros "O".
    iMod (own_update with "O") as "$"; last done.
    by apply cmra_update_exclusive.
  Qed.

  Lemma offer_agree γ q q' k k' :
    own_offer γ q k -∗ own_offer γ q' k' -∗ ⌜k = k'⌝.
  Proof.
    iIntros "O P".
    iCombine "O P" gives %[_ ?%to_agree_op_inv]%pair_valid.
    by unfold_leibniz.
  Qed.

  (** TODO: Implement Fractional and AsFractional instances *)
  Lemma offer_split γ q q' k :
    own_offer γ (q + q') k ⊣⊢ own_offer γ q k ∗ own_offer γ q' k.
  Proof.
    rewrite -own_op /own_offer.
    rewrite /offer_elm.
    rewrite -Cinr_op -pair_op.
    rewrite frac_op.
    by rewrite agree_idemp.
  Qed.

  Lemma offer_combine γ q q' k k' :
    own_offer γ q k -∗ own_offer γ q' k' -∗ ⌜k = k'⌝ ∗ own_offer γ (q + q') k.
  Proof.
    iIntros "O P".
    iDestruct (offer_agree with "O P") as %<-.
    repeat iSplit; first done.
    iCombine "O P" as "O".
    rewrite -Cinr_op -pair_op frac_op.
    by rewrite agree_idemp.
  Qed.

  Lemma half_offer_combine γ k k' :
    half_offer γ k -∗ half_offer γ k' ==∗ ⌜k = k'⌝ ∗ no_offer γ.
  Proof.
    iIntros "O P".
    iDestruct (offer_agree with "O P") as %<-.
    iMod (own_update_2 _ _ _  (Cinl (Excl ())) with "O P") as "O".
    { rewrite -Cinr_op -pair_op frac_op Qp.half_half.
      apply cmra_update_exclusive. done. }
    iModIntro. iFrame. done.
  Qed.

  Lemma no_offer_to_offers γ k : no_offer γ ==∗ own_offer γ (3/4) k ∗ quarter_offer γ k.
  Proof.
    iIntros "O".
    iMod (no_offer_to_offer with "O") as "O".
    rewrite -{1}Qp.three_quarter_quarter.
    iDestruct (offer_split with "O") as "[Hhalf Hhalf']".
    iModIntro. iFrame.
  Qed.

End offer_theory.

Section proofs.
  Context `{!relocG Σ, !lockG Σ, !offerPreG Σ}.

  Definition offer_token γ q := own γ (q : frac).

  Lemma offer_token_split γ : own γ 1%Qp ⊣⊢ own γ (1/2)%Qp ∗ own γ (1/2)%Qp.
  Proof. rewrite -{1}Qp.half_half. rewrite -own_op. done. Qed.

  (* The specification thread `k` is about to run a flip. *)
  Definition tp_flip k bf lk := (refines_right k (blueFlip #bf lk))%I.

  (* The specification thread `k` is done flipping. *)
  Definition tp_flip_done k := (refines_right k (of_val #()))%I.

  (** The offer invariant *)
  Definition I_offer γ γ' (l : loc) bf lk : iProp Σ := ∃ (n : nat),
    l ↦ #n ∗
    (⌜n = 0⌝ ∗ offer_token γ' 1 ∗ no_offer γ (* No offer, everyone is free to make one. *)
    ∨ (∃ k, (* The side channel is being used. *)
          ⌜n = 1⌝ ∗ own_offer γ (1/2) k ∗ (refines_right k (blueFlip #bf lk)) (* An offer is made. *)
        ∨ ⌜n = 2⌝ ∗ (own_offer γ (1/2) k ∗ (refines_right k #()) ∨ offer_token γ' (1/2)))). (* An offer is accepted. *)

  Definition I γ γ' (rf bf chan : loc) lk : iProp Σ :=
    ∃ (b : bool),
      is_locked_r lk false ∗
      rf ↦ #b ∗ bf ↦ₛ #b ∗
      I_offer γ γ' chan bf lk.

  Definition iN := nroot .@ "invariant".

  (* When you take an offer you have to step whoever made the offer's
     specification thread forward. *)
  Lemma take_offer_l γ γ' l bf lk E t A K :
    (|={⊤, E}=> ▷ I_offer γ γ' l bf lk ∗
      ▷ ((I_offer γ γ' l bf lk -∗ REL fill K (of_val #false) << t @ E : A)
        ∧ (∀ k, tp_flip k bf lk -∗ (tp_flip_done k -∗ I_offer γ γ' l bf lk) -∗
            REL fill K (of_val #true) << t @ E : A))) -∗
    REL fill K (CAS #l #1 #2) << t : A.
  Proof.
    iIntros "Hlog".
    rel_cmpxchg_l_atomic.
    iMod "Hlog" as "(Hoff & Hcont)".
    iDestruct "Hoff" as (n) "[lPts Hdisj]".
    iModIntro. iExists _. iFrame "lPts". iSplit.
    - iIntros (Hneq).
      iNext. iIntros "lPts".
      rel_pures_l.
      iDestruct "Hcont" as "[Hcont _]".
      iApply "Hcont".
      iExists _. iFrame.
    - iIntros ([= Heq]).
      iNext. iIntros "lPts".
      iDestruct "Hdisj" as "[[% _] | Hdisj]"; first by subst.
      iDestruct "Hdisj" as (k) "[(_ & Hoff & Hs) | [% _]]"; last by subst.
      iDestruct "Hcont" as "[_ Hcont]".
      rel_pures_l.
      iApply ("Hcont" with "Hs").
      iIntros "HI". iExists 2. iFrame "lPts".
      iRight. iExists _. iRight. iFrame. iSplit; first done. iLeft. iFrame.
  Qed.

  Lemma blue_refines_red :
    ⊢ REL redFlag << blueFlag : () → (() → lrel_bool) * (() → ()).
  Proof.
    rewrite /redFlag /blueFlag.
    rel_arrow_val. iIntros (?? [-> ->]).
    rel_pures_l.
    rel_pures_r.
    (* Implementation initialization. *)
    rel_alloc_l rf as "rfPts".
    rel_alloc_l chan as "chanPts".
    rel_pures_l.
    (* Specification initialization. *)
    rel_alloc_r bf as "bfPts".
    rel_pures_r.
    rel_apply_r refines_newlock_r. iIntros (lk) "Hlk".
    do 2 rel_pure_r.
    (* Allocate the invariant. *)
    iMod no_offer_alloc as (γ) "Hno".
    iMod (own_alloc (1%Qp)) as (γ') "Htok"; first done.
    iMod (inv_alloc iN _ (I γ γ' rf bf chan lk) with "[-]") as "#Hinv".
    { iNext. iFrame. iExists 0. iFrame. iLeft. iFrame. done. }
    iApply refines_pair.

    (* Refines read. *)
    - rel_rec_l.
      rel_arrow_val. iIntros (?? [-> ->]).
      rel_pures_l.
      rel_pures_r.
      rel_load_l_atomic.
      iInv iN as (?) "(>Hlk & rfPts & bfPts & chanPts)" "Hclose".
      iExists _. iFrame "rfPts". iModIntro. iNext. iIntros "rfPts".
      rel_rec_r.
      rel_load_r.
      iMod ("Hclose" with "[-]") as "_".
      { iNext. iExists _. iFrame. }
      rel_values.

    (* Refines flip. *)
    - rel_rec_l.
      rel_pures_l.
      rel_pures_r.
      rel_arrow_val. iIntros (?? [-> ->]).
      fold blueFlip.
      rel_pures_r.
      iLöb as "IH".
      rel_pures_l.

      (* The first CAS. *)
      rel_apply_l take_offer_l.
      iInv iN as (?) "(>Hlk & rfPts & bfPts & Hchan)" "Hclose".
      iModIntro. iFrame "Hchan". iNext. iSplit.
      (* Taking the offer succeeded. *)
      2: {
        iIntros (j) "Hj Hrest".

        (* Step our specification forward for our LP. *)
        rewrite /blueFlip.
        rel_pures_r.
        rel_apply_r (refines_acquire_r with "Hlk"). iIntros "Hlk".
        rel_load_r.
        rel_store_r.
        rel_pures_r.
        rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".

        (* Step the other thread's spec forward for their LP. *)
        rewrite /tp_flip /tp_flip_done.
        tp_rec j. tp_pures j.
        (* Handle the acquire. *)
        tp_rec j.
        rewrite /is_locked_r. iDestruct "Hlk" as (lk' ->) "Hl".
        tp_cmpxchg_suc j.
        tp_pures j.
        tp_load j.
        tp_pures j.
        tp_store j.
        tp_pures j.
        tp_rec j. tp_store j.
        rewrite negb_involutive.

        iDestruct ("Hrest" with "Hj") as "Hoff".
        iMod ("Hclose" with "[-]") as "_".
        { by iFrame. }
        rel_pures_l.
        rel_values. }
      iIntros "Hoff".
      iMod ("Hclose" with "[$]") as "_".
      rel_pures_l.

      (* The second CAS. *)
      rel_cmpxchg_l_atomic.
      iInv iN as (?) "(>Hlk & rfPts & bfPts & Hchan)" "Hclose".
      iFrame "rfPts". iModIntro. iSplit.
      2: {
        iIntros ([= ->]). iNext. iIntros "rfPts".
        rel_pures_l.
        rel_rec_r.
        rel_pures_r.
        rel_apply_r (refines_acquire_r with "Hlk"). iIntros "Hlk".
        rel_load_r.
        rel_store_r.
        rel_pures_r.
        rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        iMod ("Hclose" with "[-]") as "_". { iNext. iExists _. iFrame. }
        rel_values. }
      iIntros (_). iNext. iIntros "rfPts".
      iMod ("Hclose" with "[-]") as "_". { iNext. iExists _. iFrame. }
      rel_pures_l.

      (* The third CAS. *)
      rel_cmpxchg_l_atomic.
      iInv iN as (?) "(>Hlk & rfPts & bfPts & Hchan)" "Hclose".
      iExists _. iFrame "rfPts". iModIntro. iSplit.
      2: {
        iIntros ([= ->]). iNext. iIntros "rfPts".
        rel_pures_l.
        rel_rec_r.
        rel_pures_r.
        rel_apply_r (refines_acquire_r with "Hlk"). iIntros "Hlk".
        rel_load_r.
        rel_store_r.
        rel_pures_r.
        rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        iMod ("Hclose" with "[-]") as "_". { iNext. iExists _. iFrame. }
        rel_values. }
      iIntros (_). iNext. iIntros "rfPts".
      iMod ("Hclose" with "[-]") as "_". { iNext. iExists _. iFrame. }
      rel_pures_l.

      (* ALTERNATIVE fourth CAS. *)
      iApply refines_split.
      iIntros (k) "Hk".
      rel_cmpxchg_l_atomic.
      iInv iN as (?) "(>Hlk & rfPts & bfPts & Hchan)" "Hclose".
      iDestruct "Hchan" as (n) "[>chanPts Hdisj]".
      iModIntro. iExists _. iFrame. iSplit.
      { (* If the CAS fails we didn't succeed in making and offer, we recurse
           and use the IH. *)
        iIntros (Heq). simplify_eq/=.
        iNext. iIntros "Hchan".
        iMod ("Hclose" with "[$]") as "_".
        iApply (refines_combine with "[] Hk").
        do 2 rel_pure_l _.
        iApply "IH". }

      iIntros (Heq). simplify_eq/=.
      assert (n = 0) as -> by lia.
      iNext. iIntros "Hchan".
      iDestruct "Hdisj" as "[(_ & Htok & Hoff) | Hdisj]".
      2: { iDestruct "Hdisj" as (?) "[[% _]|[% _]]"; by subst. }
      iMod (no_offer_to_offer _ k  with "Hoff") as "Hoff".
      iEval (rewrite -Qp.half_half) in "Hoff".
      iDestruct (offer_split with "Hoff") as "[Hoff Hoff']".
      iMod ("Hclose" with "[-IH Hoff Htok]") as "_".
      { iNext. iExists _. iFrame. iExists 1. iFrame. iRight. iExists k. iLeft. by iFrame. }
      rel_pures_l.

      rel_cmpxchg_l_atomic.
      iInv iN as (?) "(>Hlk & rfPts & bfPts & Hchan)" "Hclose".
      iDestruct "Hchan" as (n) "[>chanPts Hdisj]".
      iModIntro. iExists _. iFrame "chanPts". iSplit.
      2: { (* Revoking the offer succeeded. *)
        iIntros (?) "!> Hchan". simplify_eq/=.
        assert (n = 1) as -> by lia.
        iDestruct "Hdisj" as "[[% _] | Hdisj]"; first by subst.
        iDestruct "Hdisj" as (?) "[(% & Hoff' & Hj) | [% _]]"; last by subst.
        iDestruct (offer_combine with "Hoff Hoff'") as "(<- & Hoff)".
        rewrite Qp.half_half.
        iMod (offer_to_no_offer with "Hoff") as "Hoff".
        iMod ("Hclose" with "[-IH Hj]") as "_".
        { iNext. iExists _. iFrame. iExists 0. iFrame. iLeft. by iFrame. }
        do 2 rel_pure_l _.
        iApply (refines_combine with "[] Hj").
        iApply "IH". }

      iIntros (Heq2) "!> Hchan".
      iDestruct "Hdisj" as "[(% & _ & Hoff') | Hdisj]".
      { iDestruct (no_offer_exclusive with "Hoff' Hoff") as %?. done. }
      iDestruct "Hdisj" as (?) "[[% _] | (% & Hdisj)]"; first by subst.
      iDestruct "Hdisj" as "[[Hoff' Hj] | Hoff']".
      2: {
        iCombine "Htok Hoff'" gives %Hv.
        by apply Qp.not_add_le_l in Hv. }
      iDestruct (offer_combine with "Hoff Hoff'") as "(<- & Hoff)".
      iDestruct (offer_token_split with "Htok") as "[Htok Htok']".
      iMod ("Hclose" with "[-IH Hj Hoff Htok]") as "_".
      { iNext. iExists _. iFrame. iRight.
        iExists k. iRight. by iFrame. }
      rel_pures_l.

      (* Clean up the offer. *)
      rel_store_l_atomic.
      iInv iN as (?) "(>Hlk & rfPts & bfPts & Hchan)" "Hclose".
      iDestruct "Hchan" as (m) "[>chanPts Hdisj]".
      iModIntro. iExists _. iFrame "chanPts". iNext.
      iIntros "chanPts".
      iDestruct "Hdisj" as "[(_ & _ & Hoff') | Hdisj]".
      { iDestruct (no_offer_exclusive with "Hoff' Hoff") as %?. done. }
      iDestruct "Hdisj" as (?) "[(_ & Hoff' & _) | (% & Hdisj)]".
      { iDestruct (offer_combine with "Hoff Hoff'") as "(<- & Hoff)".
        rewrite Qp.half_half.
        iDestruct (own_offer_valid with "Hoff") as %Hle.
        by apply Qp.not_add_le_l in Hle. }
      iDestruct "Hdisj" as "[[Hoff' _] | Htok']".
      { iDestruct (offer_combine with "Hoff Hoff'") as "(<- & Hoff)".
        rewrite Qp.half_half.
        iDestruct (own_offer_valid with "Hoff") as %Hle.
        by apply Qp.not_add_le_l in Hle. }
      iCombine "Htok Htok'" as "Htok".
      iEval (rewrite Qp.half_half) in "Hoff".
      iMod (offer_to_no_offer with "Hoff") as "Hoff".
      iMod ("Hclose" with "[-IH Hj]") as "_".
      { iNext. iExists _. iFrame. iExists 0. iFrame. iLeft. iFrame. done. }
      iApply (refines_combine with "[] Hj"). rel_pures_l. rel_values.
  Qed.

End proofs.
