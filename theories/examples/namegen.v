(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Name Generator ADT. Example taken from "State-Dependent
Represenation Independence" by A. Ahmed, D. Dreyer, A. Rossberg. *)
From reloc Require Export reloc.
From reloc.prelude Require Import bijections.
From reloc.lib Require Export counter.

(** One version uses references for name generation, and another
version uses integers. *)
(* ∃ α. (1 → α) × (α → α → 2)                     *)
(*       ^ new name  ^                            *)
(*                   | compare names for equality *)
Definition nameGenTy : type :=
  ∃: (TUnit → TVar 0)
   * (TVar 0 → TVar 0 → TBool).

(* TODO: cannot be a value *)
Definition nameGen1 : expr :=
  (λ: <>, ref #()
  ,λ: "y" "z", "y" = "z").

Definition nameGen2 : expr :=
  let: "x" := ref #0 in
  (λ: <>, FG_increment "x";; !"x"
  ,λ: "y" "z", "y" = "z").

Section namegen_refinement.
  Context `{!relocG Σ, !pBijPreG loc nat Σ}.

  Program Definition ngR (γ : gname) : lrel Σ := LRel (λ v1 v2,
   ∃ (l : loc) (n : nat), ⌜v1 = #l%V⌝ ∗ ⌜v2 = #n⌝
                         ∗ inBij γ l n)%I.

  Definition ng_Inv (γ : gname) (c : loc) : iProp Σ :=
    (∃ (n : nat) (L : gset (loc * nat)),
        BIJ γ L ∗ c ↦ₛ #n
     ∗  [∗ set] lk ∈ L, match lk with
                        | (l, k) => l ↦ #() ∗ ⌜k ≤ n⌝
                        end)%I.

  Lemma nameGen_ref1 :
    ⊢ REL nameGen1 << nameGen2 : ∃ α, (() → α) * (α → α → lrel_bool).
  Proof.
    unfold nameGen1, nameGen2.
    rel_alloc_r c as "Hc".
    iMod alloc_empty_bij as (γ) "HB".
    pose (N:=relocN.@"ng").
    iMod (inv_alloc N _ (ng_Inv γ c) with "[-]") as "#Hinv".
    { iNext. iExists 0, ∅. iFrame.
      by rewrite big_sepS_empty. }
    iApply (refines_exists (ngR γ)).
    do 2 rel_pure_r.
    iApply refines_pair.
    - (* New name *)
      rel_pure_l. rel_pure_r.
      iApply refines_arrow.
      iAlways. iIntros (? ?) "/= _".
      rel_pure_l. rel_pure_r.
      rel_alloc_l_atomic.
      iInv N as (n L) "(HB & Hc & HL)" "Hcl".
      iModIntro. iNext. iIntros (l') "Hl'".
      rel_apply_r (FG_increment_r with "Hc").
      iIntros "Hc". repeat rel_pure_r. rel_load_r.
      iAssert (⌜(∃ y, (l', y) ∈ L) → False⌝)%I with "[HL Hl']" as %Hl'.
      { iIntros (Hy). destruct Hy as [y Hy].
        rewrite (big_sepS_elem_of _ L (l',y) Hy).
        iDestruct "HL" as "[Hl _]".
        iDestruct (gen_heap.mapsto_valid_2 with "Hl Hl'") as %Hfoo.
        compute in Hfoo. eauto. }
      iAssert (⌜(∃ x, (x, S n) ∈ L) → False⌝)%I with "[HL]" as %Hc.
      { iIntros (Hx). destruct Hx as [x Hy].
        rewrite (big_sepS_elem_of _ L (x,S n) Hy).
        iDestruct "HL" as "[_ %]". omega. }
      iMod (bij_alloc_alt _ _ γ _ l' (S n) with "HB") as "[HB #Hl'n]"; auto.
      iMod ("Hcl" with "[-]").
      { iNext.
        replace (Z.of_nat n + 1)%Z with (Z.of_nat (n + 1)); last lia.
        iExists _,_; iFrame "Hc HB".
        rewrite big_sepS_insert; last by naive_solver.
        iFrame. iSplit; first (iPureIntro; lia).
        iApply (big_sepS_mono _ _ L with "HL").
        intros [l x] Hlx. apply bi.sep_mono_r, bi.pure_mono. lia. }
      rel_values. iModIntro.
      replace (Z.of_nat n + 1)%Z with (Z.of_nat (S n)); last lia.
      iExists l', (S n); eauto.
    - (* Name comparison *)
      rel_pure_l. rel_pure_r.
      iApply refines_arrow_val.
      iAlways. iIntros (? ?) "/= #Hv".
      iDestruct "Hv" as (l n) "(% & % & #Hln)". simplify_eq.
      do 2 rel_pure_l. do 2 rel_pure_r.
      iApply refines_arrow_val.
      iAlways. iIntros (? ?) "/= #Hv".
      iDestruct "Hv" as (l' n') "(% & % & #Hl'n')". simplify_eq.
      do 2 rel_pure_l. do 2 rel_pure_r.
      iInv N as (m L) "(>HB & >Hc & HL)" "Hcl".
      iDestruct (bij_agree with "HB Hln Hl'n'") as %Hag.
      destruct (decide (l = l')) as [->|Hll].
      + assert (n = n') as -> by (apply Hag; auto).
        case_decide; last by contradiction.
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists _,_; iFrame. }
        rewrite !bool_decide_true //.
        rel_values.
      + assert (n ≠ n') as Hnn'.
        { intros Hnn. apply Hll. by apply Hag. }
        case_decide; first by simplify_eq/=.
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists _,_; iFrame. }
        rewrite !bool_decide_false //; first rel_values.
        inversion 1; simplify_eq/=.
  Qed.
End namegen_refinement.

Lemma nameGen_ctx_refinement :
  ∅ ⊨ nameGen1 ≤ctx≤ nameGen2 : nameGenTy.
Proof.
  pose (Σ := #[relocΣ;pBijΣ loc nat]).
  eapply (refines_sound Σ).
  iIntros (? Δ).
  iApply nameGen_ref1.
Qed.
