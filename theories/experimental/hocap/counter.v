(* ReLoC -- Relational logic for fine-grained concurrency *)
(** HOCAP-style specifications for the concurrent counter *)
From reloc Require Export reloc.
From reloc.lib Require Export counter lock.
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
    by intros [_ foo%to_agree_op_inv_L']%pair_valid.
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


  Lemma wkincr_l_2 E c γ K e A :
    E ## ↑ N →
    Cnt c γ -∗
    (∀ n, cnt_auth γ n ={⊤∖↑N}=∗ cnt_auth γ n ∗ ∀ m,
       (cnt_auth γ m ={⊤∖↑N, ⊤∖↑N∖E}=∗
          cnt_auth γ (n+1) ∗ REL fill K (of_val #()) << e @ (⊤∖E): A)) -∗
    REL fill K (wkincr c) << e : A.
  Proof.
    iIntros (?).
    iDestruct 1 as (l ->) "#Hcnt". iIntros "Hvs".
    rel_rec_l. rel_load_l_atomic.
    iInv N as (n1) ">[Hl Ha]" "Hcl". iModIntro.
    iExists #n1. iFrame "Hl"; iIntros "!> Hl".
    iMod ("Hvs" with "Ha") as "[Ha Hvs]".
    iMod ("Hcl" with "[Hl Ha]") as "_".
    { iNext. iExists _; by iFrame. }
    rel_pures_l. rel_store_l_atomic.
    iMod (inv_acc_strong with "Hcnt") as "[>Hcnt' Hcl]"; first by solve_ndisj.
    iDestruct "Hcnt'" as (n2) "[Hl Ha]".
    iModIntro. iExists _. iFrame "Hl". iIntros "!> Hl".
    (* iDestruct (cnt_agree_2 with "Ha Hc") as %->. *)
    iMod ("Hvs" with "Ha") as "(Ha & Href)".
    iMod ("Hcl" with "[Ha Hl]") as "_".
    { iNext. assert ((Z.of_nat n1 + 1)%Z = Z.of_nat (n1 + 1)) as -> by lia.
      iExists _. by iFrame. }
    assert (⊤ ∖ ↑N ∖ E = ⊤ ∖ E ∖ ↑N) as -> by set_solver.
    rewrite -union_difference_L; last set_solver.
    done.
  Qed.

  Lemma wkincr_l E c γ K e A q n :
    E ## ↑ N →
    Cnt c γ -∗
    cnt γ q n -∗
    (cnt_auth γ n ∗ cnt γ q n ={⊤∖↑N, ⊤∖↑N∖E}=∗
     cnt_auth γ (n+1) ∗ REL fill K (of_val #()) << e @ (⊤∖E): A) -∗
    REL fill K (wkincr c) << e : A.
  Proof.
    iIntros (?) "#Hcnt Hn Hvs".
    iApply wkincr_l_2; try done.
    iIntros (n1) "Ha".
    iDestruct (cnt_agree_2 with "Ha Hn") as %->.
    iModIntro. iFrame "Ha". iIntros (m) "Ha".
    iDestruct (cnt_agree_2 with "Ha Hn") as %->.
    iMod ("Hvs" with "[$Ha $Hn]") as "(Ha & Hvs)".
    iModIntro. by iFrame.
  Qed.

  Lemma wkincr_l_alt E c γ K e A q n :
    E ## ↑ N →
    Cnt c γ -∗
    cnt γ q n -∗
    (cnt_auth γ n ∗ cnt γ q n ={⊤∖↑N, ⊤∖↑N∖E}=∗
     cnt_auth γ (n+1) ∗ REL fill K (of_val #()) << e @ (⊤∖E): A) -∗
    REL fill K (wkincr c) << e : A.
  Proof.
    iIntros (?).
    iDestruct 1 as (l ->) "#Hcnt". iIntros "Hc Hvs".
    rel_rec_l. rel_load_l_atomic.
    iInv N as (m) ">[Hl Ha]" "Hcl". iModIntro.
    iDestruct (cnt_agree_2 with "Ha Hc") as %->.
    iExists #n. iFrame "Hl"; iIntros "!> Hl".
    iMod ("Hcl" with "[Hl Ha]") as "_".
    { iNext. iExists _; by iFrame. }
    rel_pures_l. rel_store_l_atomic.
    iMod (inv_acc_strong with "Hcnt") as "[>Hcnt' Hcl]"; first by solve_ndisj.
    iDestruct "Hcnt'" as (m) "[Hl Ha]".
    iDestruct (cnt_agree_2 with "Ha Hc") as %->.
    iModIntro. iExists _. iFrame "Hl". iIntros "!> Hl".
    iMod ("Hvs" with "[$Ha $Hc]") as "(Ha & Href)".
    iMod ("Hcl" with "[Ha Hl]") as "_".
    { iNext. assert ((Z.of_nat n + 1)%Z = Z.of_nat (n + 1)) as -> by lia.
      iExists _. by iFrame. }
    assert (⊤ ∖ ↑N ∖ E = ⊤ ∖ E ∖ ↑N) as -> by set_solver.
    rewrite -union_difference_L; last set_solver.
    done.
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

  Lemma cnt_read_l E c γ K e A :
    E ## ↑ N →
    Cnt c γ -∗
    (∀ n : nat, cnt_auth γ n ={⊤∖↑N, ⊤∖↑N∖E}=∗
                cnt_auth γ n ∗ REL fill K (of_val #n) << e @ (⊤∖E): A) -∗
    REL fill K (! c) << e : A.
  Proof.
    iIntros (?).
    iDestruct 1 as (l ->) "#Hcnt". iIntros "Hvs".
    rel_load_l_atomic.
    iMod (inv_acc_strong with "Hcnt") as "[>H Hcl]"; first by solve_ndisj.
    iDestruct "H" as (n) "[Hl Ha]". iModIntro.
    iExists #n. iFrame "Hl"; iIntros "!> Hl".
    iMod ("Hvs" with "Ha") as "[Ha Href]".
    iMod ("Hcl" with "[Hl Ha]") as "_".
    { iNext. iExists _; by iFrame. }
    assert (⊤ ∖ ↑N ∖ E = ⊤ ∖ E ∖ ↑N) as -> by set_solver.
    rewrite -union_difference_L; last set_solver.
    done.
  Qed.
End cnt_spec.

Section refinement.
  Context `{!cnt_hocapG Σ, !relocG Σ}.

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

  Definition N:=nroot.@"cnt".
  Definition N2:=nroot.@"cntr".

  Lemma incr_refinement c γ lk l :
    Cnt N c γ -∗
    inv N2 (∃ m, is_locked_r lk false ∗ cnt γ 1 m ∗ l ↦ₛ #m)%I -∗
    REL FG_increment c << CG_increment #l lk : interp TNat [].
  Proof.
    iIntros "#HCnt #HI".
    rel_apply_l (cnt_increment_l _ (↑N2) with "HCnt"); first by solve_ndisj.
    iIntros (n) "Ha".
    iMod (inv_open_cow _ ⊤ with "HI") as "[H Hcl]"; try solve_ndisj.
    iDestruct "H" as (m) ">(Hlk & Hc & Hl)".
    iDestruct (cnt_agree_2 with "Ha Hc") as %<-.
    iMod (cnt_update (n+1) with "Ha Hc") as "[Ha Hc]".
    iModIntro. iFrame "Ha".
    rel_apply_r (CG_increment_r with "Hl Hlk").
    iIntros "Hl Hlk".
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists (n+1); try iFrame.
      assert (Z.of_nat (n + 1) = Z.of_nat n + 1)%Z as -> by lia.
      done. }
    rel_values.
  Qed.

  Lemma read_refinement c γ lk l :
    Cnt N c γ -∗
    inv N2 (∃ m, is_locked_r lk false ∗ cnt γ 1 m ∗ l ↦ₛ #m)%I -∗
    REL counter_read c << counter_read #l : interp TNat [].
  Proof.
    iIntros "#HCnt #HI".
    rel_rec_l.
    rel_apply_l (cnt_read_l _ (↑N2) with "HCnt"); first by solve_ndisj.
    iIntros (n) "Ha".
    iMod (inv_open_cow _ ⊤ with "HI") as "[H Hcl]"; try solve_ndisj.
    iDestruct "H" as (m) ">(Hlk & Hc & Hl)".
    iDestruct (cnt_agree_2 with "Ha Hc") as %<-.
    iModIntro. iFrame "Ha".
    rel_apply_r (counter_read_r with "Hl"). iIntros "Hl".
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _; iFrame. }
    rel_values.
  Qed.

  Lemma FG_CG_counter_refinement :
    ⊢ REL FG_counter << CG_counter : () → (() → lrel_int) * (() → lrel_int).
  Proof.
    unfold FG_counter, CG_counter.
    iApply refines_arrow_val.
    iModIntro. iIntros (? ?) "_"; simplify_eq/=.
    rel_rec_l. rel_rec_r.
    rel_apply_r refines_newlock_r; auto.
    iIntros (lk) "Hlk".
    repeat rel_pure_r.
    rel_alloc_r c' as "Hcnt'".
    rel_alloc_l c as "Hcnt". simpl.

    iMod (Cnt_alloc N _ 0 with "Hcnt") as (γ) "[#HCnt Hc]".

    (* establishing the invariant *)
    iMod (inv_alloc N2 _ (∃ m, is_locked_r lk false ∗ cnt γ 1 m ∗ c' ↦ₛ #m)%I
         with "[-]") as "#Hinv".
    { iNext. iExists 0. by iFrame. }
    (* TODO: here we have to do /exactly/ 4 steps.
       The next step will reduce `(Val v1, Val v2)` to `Val (v1, v2)`,
       and the compatibility rule wouldn't be applicable *)
    do 4 rel_pure_r. do 4 rel_pure_l.
    iApply refines_pair .
    - iApply refines_arrow_val.
      iModIntro. iIntros (? ?) "_". rel_seq_l; rel_seq_r.
      iApply (incr_refinement with "HCnt Hinv").
    - iApply refines_arrow_val.
      iModIntro. iIntros (? ?) "_". rel_seq_l; rel_seq_r.
      iApply (read_refinement with "HCnt Hinv").
  Qed.

End refinement.
