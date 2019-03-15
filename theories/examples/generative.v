(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Examples from "State-Dependent Represenation Independence" by A.
Ahmed, D. Dreyer, A. Rossberg.
Those are mostly "generative ADTs". *)
From reloc Require Export reloc.
From reloc.prelude Require Import bijections.
From reloc.lib Require Export counter lock.

(** Using references for name generation *)
(* ∃ α. (1 → α) × (α → α → 2)                     *)
(*       ^ new name  ^                            *)
(*                   | compare names for equality *)
Definition nameGenTy : type := TExists (TProd (TArrow TUnit (TVar 0))
                                              (TArrow (TVar 0) (TArrow (TVar 0) TBool)))%nat.

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
                        | (l, k) => l ↦ #() ∗ ⌜k ≤ n⌝%nat
                        end)%I.

  Lemma nameGen_ref1 :
    REL nameGen1 << nameGen2 : ∃ α, (() → α) * (α → α → lrel_bool).
  Proof.
    unfold nameGen1, nameGen2.
    rel_alloc_r c as "Hc".
    iMod alloc_empty_bij as (γ) "HB".
    pose (N:=relocN.@"ng").
    iMod (inv_alloc N _ (ng_Inv γ c) with "[-]") as "#Hinv".
    { iNext. iExists 0%nat, ∅. iFrame.
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
      iExists l', (S n)%nat; eauto.
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


(** A type of cells -- basically an abstract type of references. *)
(* ∀ α, ∃ β, (α → β) × (β → α) × (β → α → ())  *)
Definition cellτ : type :=
  TForall (TExists (TProd (TProd (TArrow (TVar 1) (TVar 0))
                                 (TArrow (TVar 0) (TVar 1)))
                                 (TArrow (TVar 0) (TArrow (TVar 1) TUnit))))%nat.
(* TODO: should these be values? *)
Definition cell1 : expr :=
  (Λ: (λ: "x", ref "x", λ: "r", !"r", λ: "r" "x", "r" <- "x")).

Definition cell2 : expr :=
  Λ: ( λ: "x",
       let: "r1" := ref #false in
       let: "r2" := ref "x" in
       let: "r3" := ref "x" in
       let: "lk" := newlock #() in
       ("r1", "r2", "r3", "lk")
     ,  λ: "r", let: "l" := (Snd "r") in
                acquire "l";;
                let: "v" :=
                   if: !(Fst (Fst (Fst "r")))
                   then !(Snd (Fst "r"))
                   else !(Snd (Fst (Fst "r"))) in
                release "l";;
                "v"
     , λ: "r" "x", let: "l" := (Snd "r") in
                   acquire "l";;
                   (if: !(Fst (Fst (Fst "r")))
                    then (Snd (Fst (Fst "r"))) <- "x";;
                         (Fst (Fst (Fst "r"))) <- #false
                    else (Snd (Fst "r")) <- "x";;
                         (Fst (Fst (Fst "r"))) <- #true);;
                   release "l").

Section cell_refinement.
  Context `{relocG Σ, lockG Σ}.

  Definition lockR (R : lrel Σ) (r1 r2 r3 r : loc) : iProp Σ :=
    (∃ (a b c : val), r ↦ₛ a ∗ r2 ↦ b ∗ r3 ↦ c ∗
     ( (r1 ↦ #true ∗ R c a)
     ∨ (r1 ↦ #false ∗ R b a)))%I.

  Definition cellInt (R : lrel Σ) (r1 r2 r3 l r : loc) : iProp Σ :=
    (∃ γ N, is_lock N γ #l (lockR R r1 r2 r3 r))%I.

  Program Definition cellR (R : lrel Σ) : lrel Σ := LRel (λ v1 v2,
    ∃ r1 r2 r3 l r : loc, ⌜v1 = (#r1, #r2, #r3, #l)%V⌝ ∗ ⌜v2 = #r⌝
     ∗ cellInt R r1 r2 r3 l r)%I.

  Lemma cell2_cell1_refinement :
    REL cell2 << cell1 : ∀ α, ∃ β, (α → β) * (β → α) * (β → α → ()).
  Proof.
    (* TODO: this uuugly *)
    pose (τ := (TExists (TProd (TProd (TArrow (TVar 1) (TVar 0))
                                 (TArrow (TVar 0) (TVar 1)))
                                 (TArrow (TVar 0) (TArrow (TVar 1) TUnit))))%nat).
    iPoseProof (bin_log_related_tlam [] ∅ _ _ τ) as "H".
    iSpecialize ("H" with "[]"); last first.
    { rewrite /bin_log_related.
      iSpecialize ("H" $! ∅ with "[]").
      - rewrite fmap_empty. iApply env_ltyped2_empty.
      - rewrite !fmap_empty !subst_map_empty.
        iSimpl in "H". iApply "H". }
    iIntros (R) "!#".
    iApply (bin_log_related_pack (cellR R)).
    iIntros (vs) "Hvs". rewrite !fmap_empty env_ltyped2_empty_inv.
    iDestruct "Hvs" as %->. rewrite !fmap_empty !subst_map_empty.
    iSimpl. repeat iApply refines_pair.
    - (* New cell *)
      rel_pure_l. rel_pure_r.
      iApply refines_arrow_val.
      iAlways. iIntros (v1 v2) "/= #Hv".
      rel_let_l. rel_let_r.
      rel_alloc_r r as "Hr".

      rel_alloc_l r1 as "Hr1". repeat rel_pure_l.
      rel_alloc_l r2 as "Hr2". repeat rel_pure_l.
      rel_alloc_l r3 as "Hr3". repeat rel_pure_l.

      pose (N:=relocN.@(r1,r)).
      rel_apply_l (refines_newlock_l N (lockR R r1 r2 r3 r)%I with "[-]").
      { iExists _,_,_. iFrame.
        iRight. by iFrame. }

      iNext. iIntros (lk γl) "#Hlk".
      repeat rel_pure_l. rel_values. iModIntro.
      iExists _,_,_,_,_. repeat iSplit; eauto.
      iExists _,_. by iFrame.
    - (* Read cell *)
      rel_pure_l. rel_pure_r.
      iApply refines_arrow_val.
      iAlways. iIntros (v1 v2) "/=".
      iDestruct 1 as (r1 r2 r3 l r) "[% [% #Hrs]]". simplify_eq.
      repeat rel_pure_l.
      rewrite /cellInt. iDestruct "Hrs" as (γlk N) "#Hlk".
      rel_apply_l (refines_acquire_l with "Hlk"); first auto.
      iNext. iIntros "Htok".
      rewrite /lockR. iDestruct 1 as (a b c) "(Hr & Hr2 & Hr3 & Hr1)".
      repeat rel_pure_l.
      rel_let_r. rel_load_r.
      iDestruct "Hr1" as "[[Hr1 #Ha] | [Hr1 #Ha]]";
        rel_load_l; repeat rel_pure_l; rel_load_l; repeat rel_pure_l.
      + rel_apply_l (refines_release_l with "Hlk Htok [-]"); auto.
        { iExists a,b,c; iFrame. iLeft; by iFrame. }
        iNext. repeat rel_pure_l. rel_values.
      + rel_apply_l (refines_release_l with "Hlk Htok [-]"); auto.
        { iExists _,_,_; iFrame. iRight; by iFrame. }
        iNext. repeat rel_pure_l. rel_values.
    - (* Insert cell *)
      rel_pure_l. rel_pure_r.
      iApply refines_arrow_val.
      iAlways. iIntros (v1 v2) "/=".
      iDestruct 1 as (r1 r2 r3 l r) "[% [% #Hrs]]". simplify_eq.
      repeat rel_pure_l. repeat rel_pure_r.
      iApply refines_arrow_val.
      iAlways. iIntros (v1 v2) "/= #Hv".
      repeat rel_pure_l. repeat rel_pure_r.
      rewrite /cellInt. iDestruct "Hrs" as (γlk N) "#Hlk".
      rel_apply_l (refines_acquire_l with "Hlk"); first auto.
      iNext. iIntros "Htok".
      rewrite /lockR. iDestruct 1 as (a b c) "(Hr & Hr2 & Hr3 & Hr1)".
      repeat rel_pure_l. rel_store_r.
      iDestruct "Hr1" as "[[Hr1 #Ha] | [Hr1 #Ha]]";
        rel_load_l;
        repeat rel_pure_l; rel_store_l; repeat rel_pure_l;
        repeat rel_pure_l; rel_store_l; repeat rel_pure_l.
      + rel_apply_l (refines_release_l with "Hlk Htok [-]"); auto.
        { iExists _,_,_; iFrame. iRight; by iFrame. }
        iNext. rel_values.
      + rel_apply_l (refines_release_l with "Hlk Htok [-]"); auto.
        { iExists _,_,_; iFrame. iLeft; by iFrame. }
        iNext. rel_values.
    Qed.
End cell_refinement.

Lemma cell_ctx_refinement :
  ∅ ⊨ cell2 ≤ctx≤ cell1 : cellτ.
Proof.
  pose (Σ := #[relocΣ;lockΣ]).
  eapply (refines_sound Σ).
  iIntros (? Δ).
  iApply cell2_cell1_refinement.
Qed.
