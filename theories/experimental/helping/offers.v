(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Offers used to implement the stack with helping
Based on the case study <https://iris-project.org/pdfs/2017-case-study-concurrent-stacks-with-helping.pdf> *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From reloc Require Export reloc.

Definition mk_offer : val :=
  λ: "v", ("v", ref #0).
Definition revoke_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #2 then SOME (Fst "v") else NONE.
Definition take_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #1 then SOME (Fst "v") else NONE.

Definition offerR := exclR unitR.
Class offerG Σ := { offer_inG :> inG Σ offerR }.
Definition offerΣ : gFunctors := #[GFunctor offerR].
Instance subG_offerΣ {Σ} : subG offerΣ Σ → offerG Σ.
Proof. solve_inG. Qed.

Section rules.
  Context `{!relocG Σ, !offerG Σ}.

  Definition offer_token γ := own γ (Excl ()).

  Lemma offer_token_exclusive γ : offer_token γ -∗ offer_token γ -∗ False.
  Proof. iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %[]. Qed.

  (** The offer invariant *)
  Definition is_offer γ (l : loc) (P Q : iProp Σ) :=
    (∃ (c : nat), l ↦ #c ∗
        (⌜c = 0⌝ ∗ P
       ∨ ⌜c = 1⌝ ∗ (Q ∨ offer_token γ)
       ∨ ⌜c = 2⌝ ∗ offer_token γ))%I.

  Lemma is_offer_exclusive γ1 γ2 l P1 Q1 P2 Q2 :
    is_offer γ1 l P1 Q1 -∗ is_offer γ2 l P2 Q2 -∗ False.
  Proof.
    iDestruct 1 as (?) "[Hl1 _]". iDestruct 1 as (?) "[Hl2 _]".
    iDestruct (gen_heap.mapsto_valid_2 with "Hl1 Hl2") as %[??]. contradiction.
  Qed.

  Lemma make_is_offer γ l P Q : l ↦ #0 -∗ P -∗ is_offer γ l P Q.
  Proof. iIntros "Hl HP". iExists 0; by eauto with iFrame. Qed.

  Lemma mk_offer_l K (v : val) t A :
    (∀ γ l, (∀ P Q, P -∗ is_offer γ l P Q) -∗ offer_token γ -∗ REL fill K (of_val (v, #l)) << t : A) -∗
    REL fill K (mk_offer v) << t : A.
  Proof.
    iIntros "Hcont". rel_rec_l. rel_alloc_l l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ". done.
    rel_pures_l. iApply ("Hcont" with "[Hl] Hγ").
    iIntros (P Q) "HP". iExists 0; eauto with iFrame.
  Qed.

  Lemma take_offer_l γ E o v t A K P Q :
    (|={⊤, E}=> ▷ is_offer γ o P Q ∗
         ▷ ((is_offer γ o P Q -∗ REL fill K (of_val NONEV) << t @ E : A)
            ∧ (P -∗ (Q -∗ is_offer γ o P Q) -∗ REL fill K (of_val $ SOMEV v) << t @ E : A))) -∗
    REL fill K (take_offer (v, #o)%V) << t : A.
  Proof.
    iIntros "Hlog". rel_rec_l. rel_pures_l.
    rel_cmpxchg_l_atomic.
    iMod "Hlog" as "(Hoff & Hcont)".
    rewrite {1}/is_offer. iDestruct "Hoff" as (c) "[Hl Hoff]".
    iModIntro. iExists _. iFrame "Hl". iSplit.
    - iIntros (?). iNext.
      iDestruct "Hcont" as "[Hcont _]".
      iIntros "Hl".
      rel_pures_l. iApply ("Hcont" with "[-]").
      iExists _; iFrame.
    - iIntros (?). simplify_eq/=.
      assert (c = 0) as -> by lia. (* :) *)
      iNext. iIntros "Hl".
      iDestruct "Hoff" as "[[% HP] | [[% ?] | [% ?]]]"; [| congruence..].
      rel_pures_l.
      iDestruct "Hcont" as "[_ Hcont]".
      iApply ("Hcont" with "HP [-]").
      iIntros "HQ". rewrite /is_offer. iExists 1.
      iFrame. iRight. iLeft. iSplit; eauto.
  Qed.

  Lemma wp_revoke_offer γ l E P Q (v : val) Φ :
    offer_token γ -∗
    ▷ (|={⊤, E}=> ▷ is_offer γ l P Q ∗
        ▷ ((is_offer γ l P Q -∗ Q ={E, ⊤}=∗ Φ NONEV)
           ∧ (is_offer γ l P Q -∗ P ={E, ⊤}=∗ Φ (SOMEV v)))) -∗
    WP (revoke_offer (of_val (v, #l))) {{ Φ }}.
  Proof.
    iIntros "Hγ Hlog". wp_rec. wp_pures.
    wp_bind (CmpXchg _ _ _). iApply wp_atomic.
    iMod "Hlog" as "(Hoff & Hcont)".
    rewrite {1}/is_offer. iDestruct "Hoff" as (c) "[Hl Hoff]".
    iModIntro. iDestruct "Hoff" as "[(>-> & HP)|[(>-> & HQ) | (>-> & Htok)]]".
    - wp_cmpxchg_suc; first fast_done.
      iDestruct "Hcont" as "[_ Hcont]".
      iMod ("Hcont" with "[-HP] HP") as "HΦ".
      { iExists 2. iFrame "Hl". iRight. iRight. eauto. }
      iModIntro. by wp_pures.
    - wp_cmpxchg_fail; first done.
      iDestruct "Hcont" as "[Hcont _]".
      iDestruct "HQ" as "[HQ | Htok]"; last first.
      { iExFalso. iApply (offer_token_exclusive with "Hγ Htok"). }
      iMod ("Hcont" with "[-HQ] HQ") as "HΦ".
      { iExists 1. iFrame "Hl". iRight. iLeft. eauto. }
      iModIntro. by wp_pures.
    - wp_cmpxchg_fail; first done.
      iExFalso. iApply (offer_token_exclusive with "Hγ Htok").
  Qed.

End rules.

Global Opaque offer_token is_offer revoke_offer take_offer mk_offer.
