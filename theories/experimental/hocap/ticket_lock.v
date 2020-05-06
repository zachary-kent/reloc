(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Ticket lock ≼ spin lock refinement using HOCAP-style specs for the counter *)
From reloc Require Export reloc.
From reloc.experimental Require Export hocap.counter.
From reloc.lib Require Import lock.
From reloc.examples Require Import ticket_lock.
Module spin_lock := reloc.lib.lock.

Section refinement.
  Context `{!relocG Σ, !tlockG Σ, !cnt_hocapG Σ}.

  (** * Invariants and abstracts for them *)
  Definition lockInv (γlo γln : gname) (γ : gname) (l' : val) : iProp Σ :=
    (∃ (o n : nat) (b : bool), cnt γlo 1 o ∗ cnt γln 1 n
   ∗ issuedTickets γ n ∗ is_locked_r l' b
   ∗ if b then ticket γ o else True)%I.

  Instance ifticket_timeless (b : bool) γ o : Timeless (if b then ticket γ o else True%I).
  Proof. destruct b; apply _. Qed.
  Instance lockInv_timeless lo ln γ l' : Timeless (lockInv lo ln γ l').
  Proof. apply _. Qed.

  Definition N := nroot.@"locked".

  Definition lockInt : lrel Σ := LRel (λ v1 v2,
    (∃ (γln γlo : gname) (co cn : val) (γ : gname),
        ⌜v1 = (co, cn)%V⌝
      ∗ Cnt (N.@"cnt1") cn γln
      ∗ Cnt (N.@"cnt2") co γlo
      ∗ inv (N.@"lock") (lockInv γlo γln γ v2)))%I.

  Local Instance lockInt_persistent w1 w2 : Persistent (lockInt w1 w2).
  Proof. apply _. Qed.

  Lemma wait_loop_refinement (co cn : val) (γlo γln γ : gname) (l' : val) (m : nat) :
    inv (N.@"lock") (lockInv γlo γln γ l') -∗
    Cnt (N.@"cnt1") cn γln -∗
    Cnt (N.@"cnt2") co γlo -∗
    ticket γ m -∗
    REL wait_loop #m (co, cn)%V << spin_lock.acquire l' : ().
  Proof.
    iIntros "#Hinv #Hcntn #Hcnto Hticket".
    iLöb as "IH". rel_rec_l.
    rel_pures_l.
    rel_apply_l (cnt_read_l _ (↑N.@"lock") with "Hcnto"); first by solve_ndisj.
    iIntros (o) "Hlo".
    iMod (inv_acc_strong with "Hinv") as "[HH Hcl]"; first solve_ndisj.
    iDestruct "HH" as (o' n b) "(>Hlo' & >Hln & >Hissued & >[Hl' Hbticket])".
    iDestruct (cnt_agree_2 with "Hlo Hlo'") as %<-.
    iModIntro. iFrame. rel_pures_l.
    case_decide; simplify_eq/=; rel_pures_l; last first.
    (* Whether the ticket is called out *)
    - iMod ("Hcl" with "[-Hticket]") as "_".
      { iNext. iExists _,_,_; by iFrame. }
      rewrite -union_difference_L; last done.
      by iApply "IH".
    - destruct b.
      { iDestruct (ticket_nondup with "Hticket Hbticket") as %[]. }
      rel_apply_r (refines_acquire_r with "Hl'").
      iIntros "Hl'".
      iMod ("Hcl" with "[-]") as "_".
      { iNext; iExists _,_,_; iFrame. }
      rewrite -union_difference_L; last done.
      rel_values.
  Qed.

  Lemma acquire_refinement :
    ⊢ REL acquire << spin_lock.acquire : (lockInt → ()).
  Proof.
    rel_arrow_val.
    iIntros (? l') "/= #Hl".
    iDestruct "Hl" as (γln γlo lo ln γ) "(-> & Hcntn & Hcnto & Hin)".
    rel_rec_l. rel_pures_l.
    rel_apply_l (cnt_increment_l _ ∅ with "Hcntn"); first by set_solver.
    (* the viewshift *)
    iIntros (n) "Hln".
    iInv (N.@"lock") as (o n' b) "(Hlo & >Hln' & >Hissued & >Hb)" "Hcl".
    iDestruct (cnt_agree_2 with "Hln Hln'") as %<-.
    iMod (issueNewTicket with "Hissued") as "[Hissued Hticket]".
    iMod (cnt_update (n+1) with "Hln Hln'") as "[Hln Hln']".
    iMod ("Hcl" with "[Hissued Hlo Hln' Hb]") as "_".
    { iNext. iExists _,_,_; iFrame. assert (n+1 = S n) as -> by lia. done. }
    iFrame. rewrite !difference_empty_L. iModIntro.
    rel_pures_l. by iApply wait_loop_refinement.
  Qed.

  Lemma release_refinement :
    ⊢ REL release << spin_lock.release : (lockInt → ()).
  Proof.
    rel_arrow_val.
    iIntros (? l') "/= #Hl".
    iDestruct "Hl" as (γln γlo lo ln γ) "(-> & Hcntn & Hcnto & Hinv)".
    rel_rec_l. rel_pures_l.
    rel_apply_l (wkincr_l_2 _ (↑N.@"lock") with "Hcnto"); first solve_ndisj.
    iIntros (n) "Hlo". iModIntro. iFrame. iIntros (m) "Hlo".
    iMod (inv_acc_strong with "Hinv") as "[HH Hcl]"; first solve_ndisj.
    iDestruct "HH" as (o' n2 b) "(>Hlo' & >Hln & >Hissued & >[Hl' Hbticket])".
    iMod (cnt_update (n+1) with "Hlo Hlo'") as "[Hlo Hlo']".
    iModIntro. iFrame.
    rel_apply_r (refines_release_r with "Hl'"). iIntros "Hl'".
    iMod ("Hcl" with "[-]") as "_".
    { iNext. rewrite {2}/lockInv.
      iExists _,_,_. by iFrame. }
    rewrite -union_difference_L; last done.
    by rel_values.
  Qed.

  Lemma newlock_refinement :
    ⊢ REL newlock << spin_lock.newlock : (() → lockInt).
  Proof.
    rel_arrow_val.
    iIntros (? ?) "[% %]"; subst.
    rel_rec_l. rel_alloc_l lo as "Hlo".
    rel_alloc_l ln as "Hln". rel_pures_l.
    rel_apply_r refines_newlock_r. iIntros (l') "Hl'".
    iMod (Cnt_alloc (N.@"cnt2") _ 0 with "Hln") as (γln) "[#Hc1 Hln]".
    iMod (Cnt_alloc (N.@"cnt1") _ 0 with "Hlo") as (γlo) "[#Hc2 Hlo]".
    iMod newIssuedTickets as (γ) "Hγ".
    iMod (inv_alloc (N.@"lock") _ (lockInv γln γlo γ l') with "[-]") as "#Hinv".
    { iNext. iExists 0%nat,0%nat,_. iFrame. }
    rel_values. iModIntro. iExists _,_,_,_,_. iSplit; eauto with iFrame.
  Qed.

  Lemma ticket_lock_refinement Δ :
    ⊢ REL (newlock, acquire, release)
            <<
           (spin_lock.newlock, spin_lock.acquire, spin_lock.release) : interp lockT Δ.
  Proof.
    iApply (refines_exists lockInt).
    repeat iApply refines_pair; simpl.
    - by iApply newlock_refinement.
    - by iApply acquire_refinement.
    - by iApply release_refinement.
  Qed.

End refinement.

