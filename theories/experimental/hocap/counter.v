From reloc Require Export reloc.
From reloc.lib Require Export counter.
From iris.algebra Require Export auth frac excl.
From iris.bi.lib Require Export fractional.
From iris.base_logic.lib Require Export auth.

Class cnt_hocapG Σ := CntG {
    cnt_hocapG_inG :> authG Σ (optionUR (prodR fracR (agreeR natO)));
}.

Definition cnt_hocapΣ := authΣ (optionUR (prodR fracR (agreeR natO))).

Instance sub_cnt {Σ} : subG cnt_hocapΣ Σ → cnt_hocapG Σ.
Proof. solve_inG. Qed.

Section cnt_model.
  Context `{!cnt_hocapG Σ}.

  Definition cnt_auth γ (n : nat) := (own γ (● Some (1%Qp, to_agree n)))%I.
  Definition cnt γ (q : frac) (n : nat) :=
    (own γ (◯ (Some (q, to_agree n))))%I.

  Global Instance cnt_fractional γ n :
    Fractional (λ q, cnt γ q n).
  Proof. rewrite /cnt.
    intros p q. iSplit.
    - by iDestruct 1 as "[$ $]".
    - iDestruct 1 as "[H1 H2]". by iCombine "H1 H2" as "H".
  Qed.

  Global Instance cnt_as_fractional γ n q :
    AsFractional (cnt γ q n) (λ q, cnt γ q n) q.
  Proof. split. done. apply _. Qed.

  Global Instance cnt_timeless γ n q :
    Timeless (cnt γ q n).
  Proof. apply _. Qed.

  Global Instance cnt_auth_timeless γ n :
    Timeless (cnt_auth γ n).
  Proof. apply _. Qed.

  Lemma new_cnt n :
    ⊢ |==> ∃ γ, cnt_auth γ n ∗ cnt γ 1 n.
  Proof.
    rewrite /cnt_auth /cnt.
    iMod (own_alloc (● (Some (1%Qp, to_agree n))⋅
            ◯ (Some (1%Qp, to_agree n)))) as (γ) "H".
    { apply auth_both_valid. split; done. }
    iModIntro. iExists γ. by rewrite -own_op.
  Qed.

  Lemma cnt_update k γ n m :
      cnt_auth γ n -∗ cnt γ 1 m
      ==∗
      cnt_auth γ k ∗ cnt γ 1 k.
  Proof.
    apply (bi.wand_intro_r (cnt_auth γ n)).
    rewrite /cnt /cnt_auth - !own_op.
    apply own_update. apply auth_update, option_local_update.
    by apply exclusive_local_update.
  Qed.

  Lemma cnt_agree γ q1 q2 n m :
    cnt γ q1 n -∗ cnt γ q2 m -∗ ⌜n = m⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hfoo.
    iPureIntro. revert Hfoo.
    rewrite -auth_frag_op -Some_op -pair_op.
    rewrite auth_frag_valid Some_valid.
    by intros [_ foo%agree_op_invL']%pair_valid.
  Qed.

  Lemma cnt_agree_2 γ q n m :
    cnt_auth γ n -∗ cnt γ q m -∗ ⌜n = m⌝.
  Proof.
    apply bi.wand_intro_r. rewrite /cnt /cnt_auth - !own_op.
    iIntros "H". iDestruct (own_valid with "H") as %Hfoo.
    iPureIntro; revert Hfoo.
    rewrite auth_both_valid.
    intros [[_ foo%to_agree_included]%Some_pair_included_total_2 _].
    by unfold_leibniz.
  Qed.

End cnt_model.

Section cnt_spec.
  Context `{!cnt_hocapG Σ, !relocG Σ}.
  Variable (N : namespace).

  Definition Cnt (v : val) (γ : gname) : iProp Σ :=
    ∃ l : loc, ⌜v = #l⌝ ∗ inv N (∃ n : nat, l ↦ #n ∗ cnt_auth γ n).

  Lemma Cnt_alloc (E : coPset) (m : nat) (l : loc) :
    (l ↦ #m) ={E}=∗ ∃ γ, Cnt #l γ ∗ cnt γ 1 m.
  Proof.
    iIntros "Hl".
    iMod (new_cnt m) as (γ) "[Ha Hc]".
    iMod (inv_alloc N _ (∃ n : nat, l ↦ #n ∗ cnt_auth γ n)%I
            with "[-Hc]") as "#H".
    { eauto with iFrame. }
    iModIntro. iExists _; iFrame. iExists _; iSplit; eauto with iFrame.
  Qed.


  (** We are going to make use of an alternative invariant opening rule: *)
  Lemma inv_open_cow (E E' : coPset) M P :
    ↑M ⊆ E → ↑M ⊆ E' →
    inv M P ={E,E∖↑M}=∗ ▷ P ∗ (▷ P ={E'∖↑M,E'}=∗ True).
  Proof.
    iIntros (? ?) "#Hinv".
    iMod (inv_acc_strong E M with "Hinv") as "[HP Hcl]"; first done.
    iFrame. iIntros "!> HP".
    iMod ("Hcl" $! E' ∖ ↑M with "HP") as "_".
    rewrite -union_difference_L; eauto.
  Qed.


(** This specification for the increment function allows us to
     1) derive the "standard" lifting of unary HOCAP specification
        (by picking E = ∅)
     2) prove the refinement w.r.t. coarse-grained counter
        (by picking E = ↑counterN) *)
  Lemma cnt_increment_l E c γ K e A :
    E ## ↑ N →
    Cnt c γ -∗
    (∀ n : nat, cnt_auth γ n ={⊤∖↑N, ⊤∖↑N∖E}=∗
                cnt_auth γ (n+1) ∗ REL fill K (of_val #n) << e @ (⊤∖E): A) -∗
    REL fill K (FG_increment c) << e : A.
  Proof.
    iIntros (?).
    iDestruct 1 as (l ->) "#Hcnt". iIntros "Hvs".
    iLöb as "IH". rel_rec_l. rel_load_l_atomic.
    iInv N as (n) "[Hl Ha]" "Hcl". iModIntro.
    iExists #n. iFrame "Hl"; iIntros "!> Hl".
    iMod ("Hcl" with "[Hl Ha]") as "_".
    { iNext. iExists _; by iFrame. }
    rel_pures_l. rel_cmpxchg_l_atomic.
    iMod (inv_acc_strong with "Hcnt") as "[>Hcnt' Hcl]"; first by solve_ndisj.
    iDestruct "Hcnt'" as (m) "[Hl Ha]".
    iModIntro. iExists _. iFrame "Hl". iSplit; iIntros (?) "!> Hl".
    - rel_pures_l.
      iMod ("Hcl" with "[Hl Ha]") as "_".
      { iNext. iExists _. iFrame. }
      rewrite -union_difference_L; last done.
      by iApply "IH".
    - rel_pures_l. simplify_eq/=.
      iMod ("Hvs" with "Ha") as "[Ha Href]".
      iMod ("Hcl" with "[Ha Hl]") as "_".
      { iNext.
        assert ((1 + Z.of_nat n)%Z = Z.of_nat (n + 1)) as -> by lia.
        iExists _; by iFrame. }
      assert (⊤ ∖ ↑N ∖ E = ⊤ ∖ E ∖ ↑N) as -> by set_solver.
      rewrite -union_difference_L; last set_solver.
      done.
  Qed.
End cnt_spec.
