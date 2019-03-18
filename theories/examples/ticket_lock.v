(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Ticket lock refines a simple spin lock *)
From stdpp Require Import sets.
From iris.algebra Require Export auth gset excl.
From iris.base_logic Require Import auth.
From reloc Require Import reloc lib.lock lib.counter.
From iris.heap_lang.lib Require Import ticket_lock.

(* A different `acquire` funciton to showcase the atomic rule for FG_increment *)
Definition acquire : val := λ: "lk",
  let: "n" := FG_increment (Snd "lk") in
  wait_loop "n" "lk".
(* A different `release` function to showcase the rule for wkincr *)
Definition release : val := λ: "lk", wkincr (Fst "lk").

Definition lrel_lock `{relocG Σ} : lrel Σ :=
  ∃ A, (() → A) * (A → ()) * (A → ()).

Class tlockG Σ :=
  tlock_G :> authG Σ (gset_disjUR nat).
Definition tlockΣ : gFunctors :=
  #[ authΣ (gset_disjUR nat) ].
Instance subG_tlockΣ {Σ} : subG tlockΣ Σ → tlockG Σ.
Proof. solve_inG. Qed.

Definition lockPool := gset ((loc * loc * gname) * loc).
Definition lockPoolR := gsetUR ((loc * loc * gname) * loc).

Class lockPoolG Σ :=
  lockPool_inG :> authG Σ lockPoolR.
Definition lockPoolΣ := #[ authΣ lockPoolR ].
Instance subG_lockPoolΣ {Σ} : subG lockPoolΣ Σ → lockPoolG Σ.
Proof. solve_inG. Qed.

Section refinement.
  Context `{!relocG Σ, !tlockG Σ, !lockPoolG Σ}.

  (** * Basic abstractions around the concrete RA *)

  (** ticket with the id `n` *)
  Definition ticket (γ : gname) (n : nat) := own γ (◯ GSet {[ n ]}).
  (** total number of issued tickets is `n` *)
  Definition issuedTickets (γ : gname) (n : nat) := own γ (● GSet (set_seq 0 n)).

  Lemma ticket_nondup γ n : ticket γ n -∗ ticket γ n -∗ False.
  Proof.
    iIntros "Ht1 Ht2".
    iDestruct (own_valid_2 with "Ht1 Ht2") as %?%gset_disj_valid_op.
    set_solver.
  Qed.

  Lemma newIssuedTickets : (|==> ∃ γ, issuedTickets γ 0)%I.
  Proof. iMod (own_alloc (● (GSet ∅))) as (γ) "Hγ"; [done|eauto]. Qed.

  Lemma issueNewTicket γ m :
    issuedTickets γ m ==∗
    issuedTickets γ (S m) ∗ ticket γ m.
  Proof.
    iIntros "Hseq".
    iMod (own_update with "Hseq") as "[Hseq Hticket]".
    { eapply auth_update_alloc.
      eapply (gset_disj_alloc_empty_local_update _ {[ m ]}).
      apply (set_seq_S_end_disjoint 0). }
    rewrite -(set_seq_S_end_union_L 0).
    by iFrame.
  Qed.

  Instance ticket_timeless γ n : Timeless (ticket γ n).
  Proof. apply _. Qed.
  Instance issuedTickets_timeless γ n : Timeless (issuedTickets γ n).
  Proof. apply _. Qed.

  Opaque ticket issuedTickets.

  (** * Invariants and abstracts for them *)
  Definition lockInv (lo ln : loc) (γ : gname) (l' : loc) : iProp Σ :=
    (∃ (o n : nat) (b : bool), lo ↦ #o ∗ ln ↦ #n
   ∗ issuedTickets γ n ∗ l' ↦ₛ #b
   ∗ if b then ticket γ o else True)%I.

  Instance ifticket_timeless (b : bool) γ o : Timeless (if b then ticket γ o else True%I).
  Proof. destruct b; apply _. Qed.
  Instance lockInv_timeless lo ln γ l' : Timeless (lockInv lo ln γ l').
  Proof. apply _. Qed.

  Definition N := relocN.@"locked".

  Definition lockInt : lrel Σ := LRel (λ v1 v2,
    ∃ (lo ln : loc) (γ : gname) (l' : loc),
        ⌜v1 = (#lo, #ln)%V⌝ ∗ ⌜v2 = #l'⌝
      ∗ inv N (lockInv lo ln γ l'))%I.

  (** * Refinement proofs *)

  Local Ltac openI :=
    iInv N as (o n b) ">(Hlo & Hln & Hissued & Hl' & Hbticket)" "Hcl".
  Local Ltac closeI := iMod ("Hcl" with "[-]") as "_";
    first by (iNext; iExists _,_,_; iFrame).

  (* Allocating a new lock *)
  Lemma newlock_refinement :
    REL newlock << reloc.lib.lock.newlock : () → lockInt.
  Proof.
    iApply refines_arrow_val; [done|done|].
    iAlways. iIntros (? ?) "/= [% %]"; simplify_eq.
    (* Reducing to a value on the LHS *)
    rel_rec_l.
    rel_alloc_l ln as "Hln".
    rel_alloc_l lo as "Hlo".
    (* Reducing to a value on the RHS *)
    rel_apply_r refines_newlock_r.
    iIntros (l') "Hl'".
    (* Establishing the invariant *)
    iMod newIssuedTickets as (γ) "Hγ".
    iMod (inv_alloc N _ (lockInv lo ln γ l') with "[-]") as "#Hinv".
    { iNext. iExists 0%nat,0%nat,_. by iFrame. }
    rel_pure_l.
    rel_values.
    iExists _,_,_,_. iFrame "Hinv". eauto.
  Qed.

  (* Acquiring a lock *)
  (* helper lemma *)
  Lemma wait_loop_refinement (lo ln : loc) γ (l' : loc) (m : nat) :
    inv N (lockInv lo ln γ l') -∗
    ticket γ m -∗
    REL wait_loop #m (#lo, #ln)%V << reloc.lib.lock.acquire #l' : ().
  Proof.
    iIntros "#Hinv Hticket".
    rel_rec_l.
    iLöb as "IH".
    repeat rel_pure_l.
    rel_load_l_atomic.
    openI.
    iModIntro. iExists _; iFrame; iNext.
    iIntros "Hlo". repeat rel_pure_l.
    case_decide; simplify_eq/=; rel_if_l.
    (* Whether the ticket is called out *)
    - destruct b.
      { iDestruct (ticket_nondup with "Hticket Hbticket") as %[]. }
      rel_apply_r (refines_acquire_r with "Hl'").
      iIntros "Hl'".
      closeI. rel_values.
    - iMod ("Hcl" with "[-Hticket]") as "_".
      { iNext. iExists _,_,_; by iFrame. }
      rel_rec_l. by iApply "IH".
  Qed.

  (** Logically atomic spec for `acquire`.
      Parameter type: nat
      Precondition:
        λo, ∃ n, lo ↦ᵢ o ∗ ln ↦ᵢ n ∗ issuedTickets γ n
      Postcondition:
        λo, ∃ n, lo ↦ᵢ o ∗ ln ↦ᵢ n ∗ issuedTickets γ n ∗ ticket γ o *)
  Lemma acquire_l_logatomic R P γ E K lo ln t A :
    P -∗
    □ (|={⊤,E}=> ∃ o n : nat, lo ↦ #o ∗ ln ↦ #n ∗ issuedTickets γ n ∗ R o ∗
       (∀ o : nat, (∃ n : nat, lo ↦ #o ∗ ln ↦ #n ∗ issuedTickets γ n ∗ R o) ={E,⊤}=∗ True) ∧
        (∀ o : nat, (∃ n : nat, lo ↦ #o ∗ ln ↦ #n ∗ issuedTickets γ n ∗ ticket γ o ∗ R o) -∗ P -∗
            REL fill K (of_val #()) << t @ E : A))
    -∗ (REL fill K (acquire (#lo, #ln)%V) << t : A).
  Proof.
    iIntros "HP #H".
    rewrite /acquire.
    repeat rel_pure_l.
    rel_apply_l (FG_increment_atomic_l (fun n : nat => ∃ o : nat, lo ↦ #o ∗ issuedTickets γ n ∗ R o)%I P%I with "HP").
    iAlways.
    iPoseProof "H" as "H2".
    iMod "H" as (o n) "(Hlo & Hln & Hissued & HR & Hrest)". iModIntro.
    iExists _; iFrame.
    iSplitL "Hlo HR".
    { iExists _. iFrame. }
    iSplit.
    - iDestruct "Hrest" as "[H _]".
      iIntros "[Hln Ho]".
      iDestruct "Ho" as (o') "[Ho HR]".
      iApply "H".
      iExists _. iFrame.
    - iDestruct "Hrest" as "[H _]".
      iIntros "[Hln Ho] HP".
      iDestruct "Ho" as (o') "[Ho [Hissued HR]]".
      iMod (issueNewTicket with "Hissued") as "[Hissued Hm]".
      iMod ("H" with "[-HP Hm]") as "_".
      { iExists _. iFrame.
        replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
        done. }
      clear o o'.
      repeat rel_pure_l.
      iLöb as "IH".
      rel_rec_l. repeat rel_pure_l.
      rel_load_l_atomic.
      iMod "H2" as (o n') "(Hlo & Hln & Hissued & HR & Hrest)". iModIntro.
      iExists _. iFrame. iNext. iIntros "Hlo".
      repeat rel_pure_l.
      case_decide; simplify_eq/=; rel_if_l.
      (* Whether the ticket is called out *)
      + iDestruct "Hrest" as "[_ H]".
        iApply ("H" with "[-HP] HP").
        { iExists _. iFrame. }
      + iDestruct "Hrest" as "[H _]".
        iMod ("H" with "[-HP Hm]") as "_".
        { iExists _. iFrame. }
        iApply ("IH" with "HP Hm").
  Qed.

  Lemma acquire_refinement :
    REL acquire << reloc.lib.lock.acquire : lockInt → ().
  Proof.
    iApply refines_arrow_val; [done|done|].
    iAlways. iIntros (? ?) "/= #Hl".
    iDestruct "Hl" as (lo ln γ l') "(% & % & Hin)". simplify_eq/=.
    rel_apply_l (acquire_l_logatomic
                   (fun o => ∃ (b : bool),
                             l' ↦ₛ #b ∗
                             if b then ticket γ o else True)%I
                   True%I γ); first done.
    iAlways.
    openI.
    iModIntro. iExists _,_; iFrame.
    iSplitL "Hbticket Hl'".
    { iExists _. iFrame. }
    clear b o n.
    iSplit.
    - iIntros (o). iDestruct 1 as (n) "(Hlo & Hln & Hissued & Hrest)".
      iDestruct "Hrest" as (b) "[Hl' Ht]".
      iApply ("Hcl" with "[-]").
      iNext. iExists _,_,_. by iFrame.
    - iIntros (o). iDestruct 1 as (n) "(Hlo & Hln & Hissued & Ht & Hrest)".
      iIntros "_". iDestruct "Hrest" as (b) "[Hl' Ht']".
      destruct b.
      { iDestruct (ticket_nondup with "Ht Ht'") as %[]. }
      rel_apply_r (refines_acquire_r with "Hl'").
      iIntros "Hl'".
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_,_; by iFrame. }
      rel_values.
  Qed.

  Lemma acquire_refinement_direct :
    REL acquire << reloc.lib.lock.acquire : lockInt → ().
  Proof.
    iApply refines_arrow_val; [done|done|].
    iAlways. iIntros (? ?) "/= #Hl".
    iDestruct "Hl" as (lo ln γ l') "(% & % & Hin)". simplify_eq.
    rel_rec_l. repeat rel_proj_l.
    rel_apply_l (FG_increment_atomic_l (issuedTickets γ)%I True%I); first done.
    iAlways.
    openI.
    iModIntro. iExists _; iFrame.
    iSplit.
    - iIntros "[Hln ?]".
      iApply ("Hcl" with "[-]").
      iNext. iExists _,_,_; by iFrame.
    - iIntros "[Hln Hissued] _".
      iMod (issueNewTicket with "Hissued") as "[Hissued Hm]".
      iMod ("Hcl" with "[-Hm]") as "_".
      { iNext.
        replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
        iExists _,_,_; by iFrame. }
      repeat rel_pure_l.
      by iApply wait_loop_refinement.
  Qed.

  (* Releasing the lock *)
  Lemma wkincr_l x (n : nat) K t A :
    x ↦ #n -∗
    (x ↦ #(n+1) -∗ REL fill K (of_val #()) << t : A) -∗
    (REL fill K (wkincr #x) << t : A).
  Proof.
    iIntros "Hx Hlog". rel_rec_l.
    rel_load_l. rel_op_l. rel_store_l.
    by iApply "Hlog".
  Qed.

  (* Logically atomic specification for wkincr,
     cf wkIncr specification from (da Rocha Pinto, Dinsdale-Young, Gardner)
     Parameter type: nat
     Precondition: λn, x ↦ᵢ n
     Postcondition λ_, ∃ n, x ↦ᵢ (n+1)
 *)
  Lemma wkincr_atomic_l R1 R2 E K x t A :
    R2 -∗
    □ (|={⊤,E}=> ∃ n : nat, x ↦ #n ∗ R1 n ∗
       (x ↦ #n ∗ R1 n ={E,⊤}=∗ True) ∧
        ((∃ n : nat, x ↦ #(n + 1)) ∗ R1 n -∗ R2 -∗
            REL fill K (of_val #()) << t @ E : A))
    -∗ (REL fill K (wkincr #x) << t : A).
  Proof.
    iIntros "HR2 #H".
    rel_rec_l.
    iPoseProof "H" as "H2".
    rel_load_l_atomic.
    iMod "H" as (n) "[Hx [HR1 [Hrev _]]]". iModIntro.
    iExists _; iFrame. iNext. iIntros "Hx".
    iMod ("Hrev" with "[HR1 Hx]") as "_"; simpl.
    { iFrame. }
    rel_op_l.
    rel_store_l_atomic.
    iMod "H2" as (m) "[Hx [HR1 [_ Hmod]]]". iModIntro.
    iExists _; iFrame. iNext. iIntros "Hx".
    iApply ("Hmod" with "[$HR1 Hx] HR2").
    iExists _; iFrame.
  Qed.

  Lemma release_refinement :
    REL release << reloc.lib.lock.release : lockInt → ().
  Proof.
    iApply refines_arrow_val; [done|done|].
    iAlways. iIntros (? ?) "/= #Hl".
    iDestruct "Hl" as (lo ln γ l') "(% & % & Hin)". simplify_eq.
    rel_rec_l. rel_proj_l.
    pose (R := fun (o : nat) =>
                 (∃ (n : nat) (b : bool), ln ↦ #n
                 ∗ issuedTickets γ n ∗ l' ↦ₛ #b
                 ∗ if b then ticket γ o else True)%I).
    rel_apply_l (wkincr_atomic_l R True%I); first done.
    iAlways.
    openI.
    iModIntro. iExists o; iFrame "Hlo".
    rewrite {1}/R. iSplitR "Hcl".
    { iExists _,_; by iFrame. }
    iSplit.
    - iIntros "[Hlo HR]".
      unfold R. iDestruct "HR" as (n' b') "HR".
      iApply "Hcl".
      iNext. iExists _,_,_; by iFrame.
    - iIntros "[Hlo HR] _".
      iDestruct "Hlo" as (o') "Hlo".
      unfold R. iDestruct "HR" as (n' b') "(Hln & Hissued & Hl' & Hticket)".
      rel_apply_r (refines_release_r with "Hl'").
      iIntros "Hl'".
      iMod ("Hcl" with "[-]") as "_".
      { iNext.
        replace (o' + 1) with (Z.of_nat (o' + 1))%nat by lia.
        iExists (o' + 1)%nat,_,_. by iFrame. }
      rel_values.
  Qed.

  Lemma ticket_lock_refinement :
    REL (newlock, acquire, release)
        <<
        (reloc.lib.lock.newlock, reloc.lib.lock.acquire, reloc.lib.lock.release)
    : lrel_lock.
  Proof.
    simpl. iApply (refines_exists lockInt).
    repeat iApply refines_pair.
    - by iApply newlock_refinement.
    - by iApply acquire_refinement_direct.
    - by iApply release_refinement.
  Qed.

End refinement.

Open Scope nat.
Definition lockT : type :=
  ∃: (TUnit → TVar 0)
   * (TVar 0 → TUnit)
   * (TVar 0 → TUnit).

Lemma ticket_lock_ctx_refinement :
  ∅ ⊨   (newlock, acquire, release)
  ≤ctx≤ (reloc.lib.lock.newlock, reloc.lib.lock.acquire, reloc.lib.lock.release)
  : lockT.
Proof.
  pose (Σ := #[relocΣ;tlockΣ;lockPoolΣ]).
  eapply (refines_sound Σ).
  iIntros (? Δ). iApply ticket_lock_refinement.
Qed.
