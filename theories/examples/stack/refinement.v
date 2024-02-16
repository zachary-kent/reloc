(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Refinement proof for the Treiber stack *)
From reloc Require Import reloc.
From reloc.examples.stack Require Import CG_stack FG_stack.

Definition stackN := nroot.@"stack".

Section proof.
  Context `{relocG Σ}.

  Fixpoint stack_contents (v1 : loc) (ls : list val) :=
    match ls with
    | [] => v1 ↦□ NONEV
    | h::tl => ∃ (z1 : loc), v1 ↦□ SOMEV (h, #z1) ∗ stack_contents z1 tl
    end%I.

  Definition stack_link (A : lrel Σ) (v1 : loc) (v2 : val) :=
    (∃ (ls1 : list val) (ls2 : list val),
        stack_contents v1 ls1 ∗ is_stack v2 ls2 ∗
        [∗ list] v1;v2 ∈ ls1;ls2, A v1 v2)%I.

  Global Instance stack_contents_persistent v1 ls :
    Persistent (stack_contents v1 ls).
  Proof. revert v1. induction ls; apply _. Qed.

  Lemma stack_contents_agree istk ls ls' :
    stack_contents istk ls -∗ stack_contents istk ls' -∗ ⌜ls = ls'⌝.
  Proof.
    revert istk ls'. induction ls as [|h ls]; intros istk ls'; simpl.
    - iIntros "#Histk".
      destruct ls' as [|h' ls']; first by eauto.
      simpl. iDestruct 1 as (z) "[Histk' _]".
      iDestruct (pointsto_agree with "Histk' Histk") as %Hfoo.
      exfalso. naive_solver.
    - iDestruct 1 as (z) "[Histk Hls]".
      destruct ls' as [|h' ls']; simpl.
      + iIntros "Histk'".
        iDestruct (pointsto_agree with "Histk' Histk") as %Hfoo.
        exfalso. naive_solver.
      + iDestruct 1 as (z') "[Histk' Hls']".
        iDestruct (pointsto_agree with "Histk' Histk") as %Hfoo; simplify_eq/=.
        iDestruct (IHls with "Hls Hls'") as %Hbar. simplify_eq/=.
        eauto.
  Qed.

  Definition sinv (A : lrel Σ) stk stk' : iProp Σ :=
    (∃ (istk : loc), stk  ↦ #istk ∗ stack_link A istk stk')%I.

  Lemma FG_CG_push_refinement N st st' (A : lrel Σ) (v v' : val) :
    N ## relocN →
    inv N (sinv A st st') -∗
    A v v' -∗
    REL (FG_push #st v)
       <<
        (CG_locked_push st' v') : ().
  Proof.
    iIntros (?) "#Hinv #Hvv".
    rel_rec_l. iLöb as "IH".
    rel_pures_l.
    rel_load_l_atomic.
    iInv N as (isk) "(>Hstk & Hlnk)" "Hclose".
    iExists _. iFrame.
    iModIntro. iNext. iIntros "Hstk".
    iMod ("Hclose" with "[Hlnk Hstk]") as "_".
    { iExists _. by iFrame. }
    rel_pures_l.
    rel_alloc_l nstk as "Hnstk".
    rel_cmpxchg_l_atomic.
    iInv N as (isk') "(>Hstk & Hlnk)" "Hclose".
    iExists _. iFrame "Hstk".
    iModIntro. iSplit.
    - (* CmpXchg fails *)
      iIntros (?); iNext; iIntros "Hstk".
      iMod ("Hclose" with "[Hlnk Hstk]") as "_".
      { iExists _. iFrame. }
      rel_pures_l. rel_rec_l. by iApply "IH".
    - (* CmpXchg succeeds *)
      iIntros (?). simplify_eq/=. iNext. iIntros "Hstk".
      iMod (pointsto_persist with "Hnstk") as "Hnstk".
      rewrite /stack_link. iDestruct "Hlnk" as (ls1 ls2) "(Hls1 & Hls2 & #HA)".
      rel_apply_r (refines_CG_push_r with "Hls2").
      iIntros "Hls2".
      iMod ("Hclose" with "[-]").
      { iNext. rewrite {2}/sinv. iFrame.
        iExists (v::ls1). simpl. auto with iFrame. }
      rel_pures_l. rel_values.
  Qed.

  Lemma FG_CG_pop_refinement N st st' (A : lrel Σ) :
    N ## relocN →
    inv N (sinv A st st') -∗
    REL FG_pop #st
      <<
        CG_locked_pop st' : () + A.
  Proof.
    iIntros (?) "#Hinv".
    iLöb as "IH". rel_rec_l.
    rel_load_l_atomic.
    iInv N as (istk) "(>Hstk & Hlnk)" "Hclose".
    iExists _. iFrame "Hstk".
    iModIntro. iNext. iIntros "Hstk /=".
    rel_pures_l. rel_rec_l.
    iDestruct "Hlnk" as (ls1 ls2) "(#Hls1 & Hls2 & #HA)".
    destruct ls1 as [|h1 ls1]; iSimpl in "Hls1".
    - iDestruct (big_sepL2_length with "HA") as %Hfoo.
      assert (ls2 = []) as -> by (apply length_zero_iff_nil; done). clear Hfoo.
      rel_apply_r (refines_CG_pop_fail_r with "Hls2").
      iIntros "Hls2". simpl in *.
      iMod ("Hclose" with "[Hstk Hls2]") as "_".
      { iExists _. iFrame. iExists []. iFrame; auto. }
      rel_load_l.
      rel_pures_l. rel_values.
      iModIntro. iExists _,_. eauto.
    - iDestruct "Hls1" as (z1) "[Hls1 Hrest]".
      iMod ("Hclose" with "[Hstk Hls2]") as "_".
      { iExists _. iFrame. iExists (h1 :: ls1). simpl. auto. }
      rel_load_l. rel_pures_l.
      rel_cmpxchg_l_atomic.
      iInv N as (istk') "(>Hstk & Hlnk)" "Hclose".
      iModIntro. iExists _. iFrame "Hstk". iSplit.
      + iIntros (?). iNext. iIntros "Hstk".
        iMod ("Hclose" with "[Hstk Hlnk]") as "_".
        { iExists _. iFrame. }
        rel_pures_l. iApply "IH".
      + iIntros (?). simplify_eq/=. iNext.
        iIntros "Hstk". rel_pures_l.
        iDestruct "Hlnk" as (ls1' ls2') "(Hc2 & Hst & #HA')".
        iAssert (stack_contents istk (h1::ls1)) with "[Hls1]" as "{Hls1} Hls1".
        { simpl. iExists _. auto. }
        iDestruct (stack_contents_agree with "Hls1 Hc2") as %<-.
        iClear "HA".
        rewrite big_sepL2_cons_inv_l. iDestruct "HA'" as (h2 l2' ->) "[Hh HA]".
        rel_apply_r (refines_CG_pop_suc_r with "Hst").
        iIntros "Hst".
        iMod ("Hclose" with "[-]") as "_".
        { iExists _. iFrame. iExists _; auto. }
        rel_values. iModIntro. iExists _,_; eauto.
  Qed.

  Definition stackInt A : lrel Σ := LRel (λ v1 v2,
    ∃ (stk : loc), ⌜v1 = #stk⌝
      ∗ inv (stackN .@ (stk,v2)) (sinv A stk v2))%I.

  Lemma stack_refinement :
    ⊢ REL FG_stack << CG_stack : ∀ A, ∃ B, (() → B) * (B → () + A) * (B → A → ()).
  Proof.
    unfold CG_stack, FG_stack.
    iApply refines_forall. iIntros (A). iModIntro.
    iApply (refines_pack (stackInt A)).
    repeat iApply refines_pair.
    - unfold CG_new_stack, FG_new_stack.
      iApply refines_arrow_val. iModIntro.
      iIntros (??) "_". repeat rel_pure_l. repeat rel_pure_r.
      rel_alloc_l istk as "Hisk".
      rel_alloc_l st as "Hst".
      rel_alloc_r st' as "Hst'". rel_pures_r.
      rel_apply_r refines_newlock_r. iIntros (l) "Hl". rel_pures_r.
      rel_values.
      iMod (pointsto_persist with "Hisk") as "#Hisk".
      iMod (inv_alloc (stackN.@(st,(#st', l)%V)) _ (sinv A st (#st', l)%V) with "[-]")
        as "#Hinv".
      { iNext. iExists _. iFrame. iExists [],[]. simpl.
        iSplitL "Hisk"; first by eauto.
        rewrite right_id. rewrite /is_stack. eauto with iFrame. }
      iModIntro. iExists _. eauto with iFrame.
    - rel_pure_l. rel_pure_r. iApply refines_arrow_val.
      iModIntro. iIntros (st1 st2) "Hst".
      rel_rec_l. rel_rec_r.
      iDestruct "Hst" as (??) "#Hst". simplify_eq/=.
      iApply (FG_CG_pop_refinement with "Hst").
      solve_ndisj.
    - rel_pure_l. rel_pure_r. iApply refines_arrow_val.
      iModIntro. iIntros (st1 st2) "Hst".
      rel_rec_l. rel_rec_r.
      iDestruct "Hst" as (??) "#Hst". simplify_eq/=.
      rel_pure_l. rel_pure_r. iApply refines_arrow_val.
      iModIntro. iIntros (x1 x2) "Hx".
      rel_rec_l. rel_rec_r.
      iApply (FG_CG_push_refinement with "Hst Hx").
      solve_ndisj.
  Qed.

End proof.

Open Scope nat.
Theorem stack_ctx_refinement :
  ∅ ⊨ FG_stack ≤ctx≤ CG_stack :
      ∀: ∃: (() → #0) * (#0 → () + #1) * (#0 → #1 → ()).
Proof.
  eapply (refines_sound relocΣ).
  iIntros (? ?).
  iApply stack_refinement.
Qed.
