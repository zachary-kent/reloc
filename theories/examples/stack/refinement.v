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

  Notation D := (locC -n> valC -n> iProp Σ).

  Program Definition stack_link_pre (A : lrel Σ) : D -n> D := λne S v1 v2,
    (∃ w, (∃ q, v1 ↦{q} w) ∗
      ((⌜w = NONEV⌝ ∧ ⌜v2 = NONEV⌝)
      ∨(∃ (y1 : val) (z1 : loc) (y2 z2 : val),
           ⌜w = SOMEV (y1, #z1)⌝
         ∗ ⌜v2 = SOMEV (y2, z2)⌝
         ∗ A y1 y2 ∗ ▷ S z1 z2)))%I.
  Solve Obligations with solve_proper.

  Global Instance stack_link_pre_contractive A : Contractive (stack_link_pre A).
  Proof. solve_contractive. Qed.

  Definition stack_link A := fixpoint (stack_link_pre A).

  Lemma stack_link_unfold (A : lrel Σ) (istk : loc) (v : val) :
    stack_link A istk v ≡
    (∃ w, (∃ q, istk ↦{q} w) ∗
      ((⌜w = NONEV⌝ ∧ ⌜v = NONEV⌝)
      ∨ (∃ (y1 : val) (z1 : loc) (y2 z2 : val),
            ⌜w = SOMEV (y1,#z1)⌝
          ∗ ⌜v = SOMEV (y2, z2)⌝
          ∗ A y1 y2
          ∗ ▷ stack_link A z1 z2)))%I.
  Proof.
    rewrite {1}/stack_link.
    transitivity (stack_link_pre A (fixpoint (stack_link_pre A)) istk v).
    (* TODO: rewrite fixpoint_unfold. *)
    { f_equiv. f_equiv. apply fixpoint_unfold. }
    reflexivity.
  Qed.

  (** Actually, the whole `stack_link` predicate is duplicable *)
  Local Instance stack_link_intoand (A : lrel Σ) (istk : loc) (v : val) :
    IntoSep (stack_link A istk v) (stack_link A istk v) (stack_link A istk v).
  Proof.
    rewrite /IntoSep /=. iLöb as "IH" forall (istk v).
    rewrite {1 2 3}stack_link_unfold.
    iDestruct 1 as (w) "([Histk Histk2] & [HLK | HLK])".
    - iDestruct "HLK" as "[% %]".
      iSplitL "Histk"; iExists _; iFrame; eauto.
    - iDestruct "HLK" as (y1 z1 y2 z2) "(% & % & #HQ & HLK)".
      iDestruct ("IH" with "HLK") as "[HLK HLK2]".
      iClear "IH".
      iSplitL "Histk HLK"; iExists _; iFrame; iRight; iExists _,_,_,_; eauto.
  Qed.

  Definition sinv (A : lrel Σ) stk stk' l' : iProp Σ :=
    (∃ (istk : loc) v,
       stk' ↦ₛ v
     ∗ is_lock_r l' Unlocked_r
     ∗ stk  ↦ #istk
     ∗ stack_link A istk v)%I.

  Ltac close_sinv Hcl asn :=
    iMod (Hcl with asn) as "_";
    [iNext; rewrite /sinv; iExists _,_; by iFrame |]; try iModIntro.

  Lemma FG_CG_push_refinement N st st' (A : lrel Σ) l (v v' : val) :
    N ## relocN →
    inv N (sinv A st st' l) -∗
    A v v' -∗
    REL (FG_push #st v)
       <<
        (CG_locked_push (#st', l)%V v') : ().
  Proof.
    iIntros (?) "#Hinv #Hvv".
    rel_rec_l. iLöb as "IH".
    repeat rel_pure_l.
    rel_load_l_atomic.
    iInv N as (istk w) "(>Hst' & >Hl & >Hst & HLK)" "Hclose".
    iExists _. iFrame.
    iModIntro. iNext. iIntros "Hst".
    close_sinv "Hclose" "[Hst Hst' Hl HLK]". clear w.
    repeat rel_pure_l.
    rel_alloc_l nstk as "Hnstk".
    rel_cas_l_atomic.
    iInv N as (istk' w) "(>Hst' & >Hl & >Hst & HLK)" "Hclose".
    iExists _. iFrame "Hst".
    iModIntro. iSplit.
    - (* CAS fails *)
      iIntros (?); iNext; iIntros "Hst".
      close_sinv "Hclose" "[Hst Hst' Hl HLK]". clear w.
      rel_if_false_l. simpl.
      rel_rec_l.
      by iApply "IH".
    - (* CAS succeeds *)
      iIntros (?). simplify_eq/=. iNext. iIntros "Hst".
      rel_apply_r (refines_CG_push_r with "Hst' Hl").
      iIntros "Hst' Hl".
      iMod ("Hclose" with "[Hst Hst' Hl HLK Hnstk]").
      { iNext. rewrite {2}/sinv. iExists _,_.
        iFrame "Hst' Hst Hl".
        rewrite (stack_link_unfold _ nstk).
        iExists _. iSplitL "Hnstk".
        - iExists 1%Qp; iFrame.
        - iRight. iExists _,_,_,_. eauto. }
      rel_if_true_l.
      rel_values.
  Qed.

  Lemma FG_CG_pop_refinement N st st' (A : lrel Σ) l :
    N ## relocN →
    inv N (sinv A st st' l) -∗
    REL FG_pop #st
      <<
        CG_locked_pop (#st', l)%V : () + A.
  Proof.
    iIntros (?) "#Hinv".
    iLöb as "IH". rel_rec_l.
    rel_load_l_atomic.
    iInv N as (istk w) "(>Hst' & >Hl & >Hst & HLK)" "Hclose".
    iExists _. iFrame "Hst".
    iModIntro. iNext. iIntros "Hst /=".
    repeat rel_pure_l. rel_rec_l.
    iDestruct "HLK" as "[HLK HLK2]".
    rewrite {1}stack_link_unfold.
    iDestruct "HLK" as (w') "(Histk & HLK)".
    iDestruct "HLK" as "[[% %] | HLK]"; simplify_eq/=.
    - (* The stack is empty *)
      rel_apply_r (refines_CG_pop_fail_r with "Hst' Hl").
      iIntros "Hst' Hl".
      (* duplicate the top node *)
      iDestruct "Histk" as "[Histk Histk2]".
      close_sinv "Hclose" "[Hst' Hst Hl HLK2]".
      iDestruct "Histk2" as (q) "Histk2".
      rel_load_l. repeat rel_pure_l.
      rel_values.
      iModIntro. iExists _,_. eauto.
    - (* The stack has a value *)
      iDestruct "HLK" as (y1 z1 y2 z2) "(% & % & #Hτ & HLK_tail)"; simplify_eq/=.
      (* duplicate the top node *)
      close_sinv "Hclose" "[Hst' Hst Hl HLK2]".
      iDestruct "Histk" as (q) "Histk".
      rel_load_l. repeat rel_pure_l.
      rel_cas_l_atomic.
      iInv N as (istk' w) "(>Hst' & >Hl & >Hst & HLK)" "Hclose".
      iExists _. iFrame "Hst".
      iModIntro. iSplit.
      + (* CAS fails *) iIntros (?); simplify_eq/=.
        iNext. iIntros "Hst".
        rel_if_l.
        close_sinv "Hclose" "[Hst Hst' Hl HLK]".
        iApply "IH".
      + (* CAS succeeds *) iIntros (?); simplify_eq/=.
        iNext. iIntros "Hst".
        rel_if_l.
        rewrite (stack_link_unfold _ istk).
        iDestruct "HLK" as (w') "(Histk2 & HLK)".
        iAssert (⌜w' = InjRV (y1, #z1)⌝)%I with "[Histk Histk2]" as %->.
        { iDestruct "Histk2" as (?) "Histk2".
          iApply (gen_heap.mapsto_agree with "Histk2 Histk"). }
        iDestruct "HLK" as "[[% %] | HLK]"; first by congruence.
        iDestruct "HLK" as (? ? ? ? ? ?) "[#Hτ2 HLK]". simplify_eq/=.
        rel_apply_r (refines_CG_pop_suc_r with "Hst' Hl").
        iIntros "Hst' Hl".
        close_sinv "Hclose" "[-]".
        rel_pure_l.
        rel_values. iModIntro. iExists _,_; eauto.
  Qed.

  Definition stackInt A : lrel Σ := LRel (λ v1 v2,
    ∃ (l : val) (stk stk' : loc), ⌜v2 = (#stk', l)%V⌝ ∗ ⌜v1 = #stk⌝
      ∗ inv (stackN .@ (stk,stk')) (sinv A stk stk' l))%I.

  Lemma stack_refinement :
    REL FG_stack << CG_stack : ∀ A, ∃ B, (() → B) * (B → () + A) * (B → A → ()).
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
      rel_apply_r refines_newlock_r. iIntros (l) "Hl".
      rel_pure_r. rel_alloc_r st' as "Hst'". rel_pure_r.
      rel_values.
      iMod (inv_alloc (stackN.@(st,st')) _ (sinv A st st' l) with "[-]")
        as "#Hinv".
      { iNext. iExists _,_. iFrame.
        rewrite stack_link_unfold. iExists _.
        iSplitL; eauto. }
      iModIntro. iExists _,_,_. iFrame "Hinv". eauto.
    - rel_pure_l. rel_pure_r. iApply refines_arrow_val.
      iAlways. iIntros (st1 st2) "Hst".
      rel_rec_l. rel_rec_r.
      iDestruct "Hst" as (??? ??) "#Hst". simplify_eq/=.
      iApply (FG_CG_pop_refinement with "Hst").
      solve_ndisj.
    - rel_pure_l. rel_pure_r. iApply refines_arrow_val.
      iAlways. iIntros (st1 st2) "Hst".
      rel_rec_l. rel_rec_r.
      iDestruct "Hst" as (??? ??) "#Hst". simplify_eq/=.
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
    ∀: ∃: (TUnit → TVar 0)
         * (TVar 0 → TUnit + TVar 1)
         * (TVar 0 → TVar 1 → TUnit).
Proof.
  eapply (refines_sound relocΣ).
  iIntros (? ?).
  iApply stack_refinement.
Qed.

