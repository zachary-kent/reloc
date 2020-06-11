(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Refinement proof for the Treiber stack *)
From reloc Require Import reloc.
From reloc.examples.stack Require Import CG_stack FG_stack.

Definition stackN := nroot.@"stack".

Section proof.
  Context `{relocG Σ}.

  (** The "partial pointsto" proposition is duplicable *)
  Local Instance istk_fromand (istk : loc) (w : val) :
    FromSep (∃ q, istk ↦{q} w) (∃ q, istk ↦{q} w) (∃ q, istk ↦{q} w).
  Proof.
    rewrite /FromSep. iIntros "[$ _]".
  Qed.
  Local Instance istk_intoand (istk : loc) (w : val) :
    IntoSep (∃ q, istk ↦{q} w) (∃ q, istk ↦{q} w) (∃ q, istk ↦{q} w).
  Proof.
    rewrite /IntoSep /=. iDestruct 1 as (q) "[H1 H2]".
    iSplitL "H1"; eauto with iFrame.
  Qed.

  Fixpoint stack_contents (v1 : loc) (ls : list val) :=
    match ls with
    | [] => ∃ q, v1 ↦{q} NONEV
    | h::tl => ∃ (z1 : loc) q, v1 ↦{q} SOMEV (h, #z1) ∗
                 stack_contents z1 tl
    end%I.

  Definition stack_link (A : lrel Σ) (v1 : loc) (v2 : val) :=
    (∃ (ls1 : list val) (ls2 : list val),
        stack_contents v1 ls1 ∗ is_stack v2 ls2 ∗
        [∗ list] v1;v2 ∈ ls1;ls2, A v1 v2)%I.

  (** Actually, the whole `stack_contents` predicate is duplicable *)
  Local Instance stack_contents_intoand (istk : loc) (ls : list val) :
    IntoSep (stack_contents istk ls) (stack_contents istk ls) (stack_contents istk ls).
  Proof.
    rewrite /IntoSep /=.
    revert istk. induction ls as [|h ls]; intros istk; simpl.
    - apply istk_intoand.
    - iDestruct 1 as (z1 q) "[Histk Hc]".
      rewrite IHls. iDestruct "Hc" as "[Hc1 Hc2]". iDestruct "Histk" as "[Histk1 Histk2]".
      iSplitL "Hc1 Histk1"; iExists _, (q/2)%Qp; by iFrame.
  Qed.

  Lemma stack_contents_agree istk ls ls' :
    stack_contents istk ls -∗ stack_contents istk ls' -∗ ⌜ls = ls'⌝.
  Proof.
    revert istk ls'. induction ls as [|h ls]; intros istk ls'; simpl.
    - iDestruct 1 as (q) "Histk".
      destruct ls' as [|h' ls']; first by eauto.
      simpl. iDestruct 1 as (z q') "[Histk' _]".
      iDestruct (gen_heap.mapsto_agree with "Histk' Histk") as %Hfoo.
      exfalso. naive_solver.
    - iDestruct 1 as (z q) "[Histk Hls]".
      destruct ls' as [|h' ls']; simpl.
      + iDestruct 1 as (q') "Histk'".
        iDestruct (gen_heap.mapsto_agree with "Histk' Histk") as %Hfoo.
        exfalso. naive_solver.
      + iDestruct 1 as (z' q') "[Histk' Hls']".
        iDestruct (gen_heap.mapsto_agree with "Histk' Histk") as %Hfoo. simplify_eq/=.
        iDestruct (IHls with "Hls Hls'") as %Hbar. simplify_eq/=.
        eauto.
  Qed.

  Definition sinv (A : lrel Σ) stk stk' : iProp Σ :=
    (∃ (istk : loc), stk  ↦ #istk ∗ stack_link A istk stk')%I.

  Ltac close_sinv Hcl asn :=
    iMod (Hcl with asn) as "_";
    [iNext; rewrite /sinv; iExists _;
         (by iFrame || iFrame; iExists _,_; by eauto with iFrame) |]; try iModIntro.

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
    close_sinv "Hclose" "[Hlnk Hstk]".
    rel_pures_l.
    rel_alloc_l nstk as "Hnstk".
    rel_cmpxchg_l_atomic.
    iInv N as (isk') "(>Hstk & Hlnk)" "Hclose".
    iExists _. iFrame "Hstk".
    iModIntro. iSplit.
    - (* CmpXchg fails *)
      iIntros (?); iNext; iIntros "Hstk".
      close_sinv "Hclose" "[Hlnk Hstk]".
      rel_pures_l. rel_rec_l. by iApply "IH".
    - (* CmpXchg succeeds *)
      iIntros (?). simplify_eq/=. iNext. iIntros "Hstk".
      rewrite /stack_link. iDestruct "Hlnk" as (ls1 ls2) "(Hls1 & Hls2 & #HA)".
      rel_apply_r (refines_CG_push_r with "Hls2").
      iIntros "Hls2".
      iMod ("Hclose" with "[-]").
      { iNext. rewrite {2}/sinv. iExists _. iFrame.
        iExists (v::ls1),_. simpl. iFrame "Hls2 Hvv HA".
        iExists _,_. iFrame. }
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
    iDestruct "Hlnk" as (ls1 ls2) "(Hls1 & Hls2 & #HA)".
    iDestruct "Hls1" as "[Histk1 Histk2]".
    destruct ls1 as [|h1 ls1]; iSimpl in "Histk1".
    - iDestruct (big_sepL2_length with "HA") as %Hfoo.
      assert (ls2 = []) as -> by (apply length_zero_iff_nil; done). clear Hfoo.
      rel_apply_r (refines_CG_pop_fail_r with "Hls2").
      iIntros "Hls2".
      close_sinv "Hclose" "[Histk2 Hstk Hls2]".
      iDestruct "Histk1" as (q) "Histk'". rel_load_l.
      rel_pures_l. rel_values.
      iModIntro. iExists _,_. eauto.
    - iDestruct "Histk1" as (z1 q) "[Histk1 Hrest]".
      close_sinv "Hclose" "[Histk2 Hstk Hls2]".
      rel_load_l. rel_pures_l.
      rel_cmpxchg_l_atomic.
      iInv N as (istk') "(>Hstk & Hlnk)" "Hclose".
      iModIntro. iExists _. iFrame "Hstk". iSplit.
      + iIntros (?). iNext. iIntros "Hstk".
        close_sinv "Hclose" "[Hstk Hlnk]".
        rel_pures_l. iApply "IH".
      + iIntros (?). simplify_eq/=. iNext.
        iIntros "Hstk". rel_pures_l.
        iDestruct "Hlnk" as (ls1' ls2') "(Hc2 & Hst & #HA')".
        iDestruct "Hrest" as "[Hrest Hz1]".
        iAssert (stack_contents istk (h1::ls1)) with "[Histk1 Hrest]" as "Histk1".
        { simpl. iExists _,_. by iFrame. }
        iDestruct (stack_contents_agree with "Histk1 Hc2") as %<-.
        iClear "HA".
        rewrite big_sepL2_cons_inv_l. iDestruct "HA'" as (h2 l2' ->) "[Hh HA]".
        rel_apply_r (refines_CG_pop_suc_r with "Hst").
        iIntros "Hst".
        close_sinv "Hclose" "[-]".
        rel_values. iModIntro. iExists _,_; eauto.
  Qed.

  Definition stackInt A : lrel Σ := LRel (λ v1 v2,
    ∃ (stk : loc), ⌜v1 = #stk⌝
      ∗ inv (stackN .@ (stk,v2)) (sinv A stk v2))%I.

  Lemma stack_refinement :
    ⊢ REL FG_stack << CG_stack : ∀ A, ∃ B, (() → B) * (B → () + A) * (B → A → ()).
  Proof.
    unfold CG_stack, FG_stack.
    iApply refines_forall. iIntros (A). iAlways.
    iApply (refines_exists (stackInt A)).
    repeat iApply refines_pair.
    - unfold CG_new_stack, FG_new_stack.
      iApply refines_arrow_val. iAlways.
      iIntros (??) "_". repeat rel_pure_l. repeat rel_pure_r.
      rel_alloc_l istk as "Hisk".
      rel_alloc_l st as "Hst".
      rel_alloc_r st' as "Hst'". rel_pures_r.
      rel_apply_r refines_newlock_r. iIntros (l) "Hl". rel_pures_r.
      rel_values.
      iMod (inv_alloc (stackN.@(st,(#st', l)%V)) _ (sinv A st (#st', l)%V) with "[-]")
        as "#Hinv".
      { iNext. iExists _. iFrame. iExists [],[]. simpl.
        iSplitL "Hisk"; first by eauto.
        rewrite right_id. rewrite /is_stack.
        iExists _,_; eauto with iFrame. }
      iModIntro. iExists _. eauto with iFrame.
    - rel_pure_l. rel_pure_r. iApply refines_arrow_val.
      iAlways. iIntros (st1 st2) "Hst".
      rel_rec_l. rel_rec_r.
      iDestruct "Hst" as (??) "#Hst". simplify_eq/=.
      iApply (FG_CG_pop_refinement with "Hst").
      solve_ndisj.
    - rel_pure_l. rel_pure_r. iApply refines_arrow_val.
      iAlways. iIntros (st1 st2) "Hst".
      rel_rec_l. rel_rec_r.
      iDestruct "Hst" as (??) "#Hst". simplify_eq/=.
      rel_pure_l. rel_pure_r. iApply refines_arrow_val.
      iAlways. iIntros (x1 x2) "Hx".
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
