(* ReLoC -- Relational logic for fine-grained concurrency *)
(** This is a generative ADT example from "State-Dependent
Represenation Independence" by A. Ahmed, D. Dreyer, A. Rossberg.

In this example we implement a symbol lookup table, where a symbol is
an abstract data type. Because the only way to obtain a symbol is to
insert something into the table, we can show that the dynamic check in
the lookup function in `symbol2` is redundant. *)
From iris.algebra Require Import auth.
From reloc Require Import reloc.
From reloc.lib Require Import lock list.

(** * Symbol table *)
Definition lrel_symbol `{relocG Σ} : lrel Σ :=
  ∃ α, (α → α → lrel_bool)    (* equality check *)
     * (lrel_int → α)          (* insert *)
     * (α → lrel_int).         (* lookup *)

Definition eqKey : val := λ: "n" "m", "n" = "m".
Definition symbol1 : val := λ: <>,
  let: "size" := ref #0 in
  let: "tbl" := ref NIL in
  let: "l" := newlock #() in
  (eqKey,
   λ: "s", acquire "l";;
           let: "n" := !"size" in
           "size" <- "n"+#1;;
           "tbl" <- CONS "s" (!"tbl");;
           release "l";;
           "n",
   λ: "n", nth (!"tbl") (!"size" - "n")).
Definition symbol2 : val := λ: <>,
  let: "size" := ref #0 in
  let: "tbl" := ref NIL in
  let: "l" := newlock #() in
  (eqKey,
   λ: "s", acquire "l";;
           let: "n" := !"size" in
           "size" <- "n"+#1;;
           "tbl" <- CONS "s" (!"tbl");;
           release "l";;
           "n",
   λ: "n", let: "m" := !"size" in
           if: "n" ≤ "m" then nth (!"tbl") (!"size" - "n") else #0).


(** * The actual refinement proof.
      Requires monotonic state *)
Class msizeG Σ := MSizeG { msize_inG :> inG Σ (authR mnatUR) }.
Definition msizeΣ : gFunctors := #[GFunctor (authR mnatUR)].

Instance subG_msizeΣ {Σ} : subG msizeΣ Σ → msizeG Σ.
Proof. solve_inG. Qed.

Section rules.
  Definition sizeN := relocN .@ "size".
  Context `{!relocG Σ, !msizeG Σ}.
  Context (γ : gname).

  Lemma size_le (n m : nat) :
    own γ (● (n : mnat)) -∗
    own γ (◯ (m : mnat)) -∗
    ⌜m ≤ n⌝%nat.
  Proof.
    iIntros "Hn Hm".
    by iDestruct (own_valid_2 with "Hn Hm")
      as %[?%mnat_included _]%auth_valid_discrete_2.
  Qed.

  Lemma same_size (n m : nat) :
    own γ (● (n : mnat)) ∗ own γ (◯ (m : mnat))
    ==∗ own γ (● (n : mnat)) ∗ own γ (◯ (n : mnat)).
  Proof.
    iIntros "[Hn Hm]".
    iMod (own_update_2 γ _ _ (● (n : mnat) ⋅ ◯ (n : mnat)) with "Hn Hm")
      as "[$ $]"; last done.
    apply auth_update, (mnat_local_update _ _ n); auto.
  Qed.

  Lemma inc_size' (n m : nat) :
    own γ (● (n : mnat)) ∗ own γ (◯ (m : mnat))
    ==∗ own γ (● (S n : mnat)).
  Proof.
    iIntros "[Hn #Hm]".
    iMod (own_update_2 γ _ _ (● (S n : mnat) ⋅ ◯ (S n : mnat)) with "Hn Hm") as "[$ _]"; last done.
    apply auth_update, (mnat_local_update _ _ (S n)); auto.
  Qed.

  Lemma conjure_0 :
    (|==> own γ (◯ (O : mnat)))%I.
  Proof. by apply own_unit. Qed.

  Lemma inc_size (n : nat) :
    own γ (● (n : mnat)) ==∗ own γ (● (S n : mnat)).
  Proof.
    iIntros "Hn".
    iMod (conjure_0) as "Hz".
    iApply inc_size'; by iFrame.
  Qed.

  Definition tableR : lrel Σ := LRel (λ v1 v2,
    (∃ n : nat, ⌜v1 = #n⌝ ∗ ⌜v2 = #n⌝ ∗ own γ (◯ (n : mnat))))%I.

  Definition table_inv (size1 size2 tbl1 tbl2 : loc) : iProp Σ :=
    (∃ (n : nat) (ls : val), own γ (● (n : mnat))
                           ∗ size1 ↦{1/2} #n ∗ size2 ↦ₛ{1/2} #n
                           ∗ tbl1 ↦{1/2} ls ∗ tbl2 ↦ₛ{1/2} ls
                           ∗ lrel_list lrel_int ls ls)%I.

  Definition lok_inv (size1 size2 tbl1 tbl2 l : loc) : iProp Σ :=
    (∃ (n : nat) (ls : val), size1 ↦{1/2} #n ∗ size2 ↦ₛ{1/2} #n
                           ∗ tbl1 ↦{1/2} ls ∗ tbl2 ↦ₛ{1/2} ls
                           ∗ l ↦ₛ #false)%I.
End rules.

Section proof.
  Context `{!relocG Σ, !msizeG Σ, !lockG Σ}.

  Lemma eqKey_refinement γ :
    REL eqKey << eqKey : tableR γ → tableR γ → lrel_bool.
  Proof.
    unlock eqKey.
    iApply refines_arrow_val.
    iAlways. iIntros (k1 k2) "/= #Hk".
    iDestruct "Hk" as (n) "(% & % & #Hn)"; simplify_eq.
    rel_let_l. rel_let_r. rel_pure_l. rel_pure_r.
    iApply refines_arrow_val.
    iAlways. iIntros (k1 k2) "/= #Hk".
    iDestruct "Hk" as (m) "(% & % & #Hm)"; simplify_eq.
    rel_let_l. rel_let_r.
    rel_op_l. rel_op_r. rel_values.
  Qed.

  Lemma lookup_refinement1 (γ : gname) (size1 size2 tbl1 tbl2 : loc) :
    inv sizeN (table_inv γ size1 size2 tbl1 tbl2) -∗
    REL
      (λ: "n", (nth ! #tbl1) (! #size1 - "n"))%V
    <<
      (λ: "n",
        let: "m" := ! #size2 in
         if: "n" ≤ "m" then (nth ! #tbl2) (! #size2 - "n") else #0)%V :
      (tableR γ → lrel_int).
  Proof.
    iIntros "#Hinv".
    unlock. iApply refines_arrow_val.
    iAlways. iIntros (k1 k2) "/= #Hk".
    iDestruct "Hk" as (n) "(% & % & #Hn)"; simplify_eq.
    rel_let_l. rel_let_r.
    rel_load_l_atomic.
    iInv sizeN as (m ls)
        "(Ha & Hs1' & Hs2' & Htbl1' & Htbl2' & #Hls)" "Hcl".
    iModIntro. iExists _. iFrame. iNext. iIntros "Hs1'".
    rel_load_r. rel_pure_r. rel_pure_r.
    iDestruct (own_valid_2 with "Ha Hn")
      as %[?%mnat_included _]%auth_valid_discrete_2.
    rel_op_l. rel_op_r. rewrite bool_decide_true; last lia.
    rel_pure_r. rel_load_r. rel_op_r.
    iMod ("Hcl" with "[Ha Hs1' Hs2' Htbl1' Htbl2' Hls]") as "_".
    { iNext. iExists _,_. iFrame. repeat iSplit; eauto. }
    iClear "Hls".
    rel_load_l_atomic.
    iInv sizeN as (m' ls')
        "(Ha & Hs1' & >Hs2' & >Htbl1' & >Htbl2' & #Hls)" "Hcl".
    iModIntro. iExists _. iFrame. iNext. iIntros "Htbl1'".
    rel_load_r.
    iMod ("Hcl" with "[Ha Hs1' Hs2' Htbl1' Htbl2' Hls]") as "_".
    { iNext. iExists _,_. iFrame. repeat iSplit; eauto. }
    repeat iApply refines_app.
    - iApply nth_int_typed.
    - rel_values.
    - rel_values.
  Qed.

  Lemma lookup_refinement2 (γ : gname) (size1 size2 tbl1 tbl2 : loc) :
    inv sizeN (table_inv γ size1 size2 tbl1 tbl2) -∗
    REL
      (λ: "n",
        let: "m" := ! #size1 in
         if: "n" ≤ "m" then (nth ! #tbl1) (! #size1 - "n") else #0)%V
    <<
      (λ: "n", (nth ! #tbl2) (! #size2 - "n"))%V : (tableR γ → lrel_int).
  Proof.
    iIntros "#Hinv".
    unlock.
    iApply refines_arrow_val.
    iAlways. iIntros (k1 k2) "#Hk /=".
    iDestruct "Hk" as (n) "(% & % & #Hn)"; simplify_eq.
    repeat rel_pure_l. repeat rel_pure_r.
    rel_load_l_atomic.
    iInv sizeN as (m ls) "(Ha & Hs1' & >Hs2' & >Htbl1' & >Htbl2' & Hls)" "Hcl".
    iModIntro. iExists _. iFrame. iNext. iIntros "Hs1'".
    iDestruct (own_valid_2 with "Ha Hn")
      as %[?%mnat_included _]%auth_valid_discrete_2.
    iMod ("Hcl" with "[Ha Hs1' Hs2' Htbl1' Htbl2' Hls]") as "_".
    { iNext. iExists _,_. by iFrame. }
    clear ls. repeat rel_pure_l.
    case_bool_decide; last by lia.
    rel_if_l.
    rel_load_l_atomic.
    iInv sizeN as (m' ls) "(Ha & Hs1' & Hs2' & Htbl1' & Htbl2' & Hls)" "Hcl".
    iModIntro. iExists _. iFrame. iNext. iIntros "Hs1'".
    rel_load_r.
    iMod ("Hcl" with "[Ha Hs1' Hs2' Htbl1' Htbl2' Hls]") as "_".
    { iNext. iExists _,_. by iFrame. }
    rel_pure_l. rel_pure_r.
    rel_load_l_atomic.
    clear ls.
    iInv sizeN as (? ls) "(Ha & Hs1' & Hs2' & Htbl1' & Htbl2' & #Hls)" "Hcl".
    iModIntro. iExists _. iFrame. iNext. iIntros "Htbl1'".
    rel_load_r.
    iMod ("Hcl" with "[Ha Hs1' Hs2' Htbl1' Htbl2']") as "_".
    { iNext. iExists _,_. by iFrame. }
    repeat iApply refines_app.
    - iApply nth_int_typed.
    - rel_values.
    - rel_values.
  Qed.

  Lemma refinement1 :
    REL symbol1 << symbol2 : () → lrel_symbol.
  Proof.
    unlock symbol1 symbol2.
    iApply refines_arrow_val.
    iAlways. iIntros (? ?) "[% %]"; simplify_eq/=.
    rel_let_l. rel_let_r.
    rel_alloc_l size1 as "[Hs1 Hs1']"; repeat rel_pure_l.
    rel_alloc_r size2 as "[Hs2 Hs2']"; repeat rel_pure_r.
    rel_alloc_l tbl1 as "[Htbl1 Htbl1']"; repeat rel_pure_l.
    rel_alloc_r tbl2 as "[Htbl2 Htbl2']"; repeat rel_pure_r.
    iMod (own_alloc (● (0%nat : mnat))) as (γ) "Ha"; first done.
    iMod (inv_alloc sizeN _ (table_inv γ size1 size2 tbl1 tbl2) with "[Hs1 Hs2 Htbl1 Htbl2 Ha]") as "#Hinv".
    { iNext. iExists _,_. iFrame. iApply lrel_list_nil. }
    rel_apply_r refines_newlock_r.
    iIntros (l2) "Hl2". rel_pure_r. rel_pure_r.
    pose (N:=(relocN.@"lock1")).
    rel_apply_l (refines_newlock_l N (lok_inv size1 size2 tbl1 tbl2 l2)%I with "[Hs1' Hs2' Htbl1' Htbl2' Hl2]").
    { iExists 0%nat,_. by iFrame. }
    iNext. iIntros (l1 γl) "#Hl1". rel_pure_l. rel_pure_l.
    iApply (refines_exists (tableR γ)).
    repeat iApply refines_pair.
    (* Eq *)
    - iApply eqKey_refinement.
    (* Insert *)
    - rel_pure_l. rel_pure_r.
      iApply refines_arrow_val.
      iAlways. iIntros (? ?). iDestruct 1 as (n) "[% %]"; simplify_eq/=.
      repeat rel_pure_l. repeat rel_pure_r.
      rel_apply_l (refines_acquire_l with "Hl1").
      iNext. iIntros "Hlk Htbl". repeat rel_pure_l.
      iDestruct "Htbl" as (m ls) "(Hs1 & Hs2 & Htbl1 & Htbl2 & Hl2)".
      rel_load_l. repeat rel_pure_l.
      rel_store_l_atomic.
      iInv sizeN as (m' ls') "(Ha & >Hs1' & >Hs2' & >Htbl1' & >Htbl2' & #Hls)" "Hcl".
      iDestruct (gen_heap.mapsto_agree with "Hs1 Hs1'") as %Hm'.
      simplify_eq/=.
      iCombine "Hs1 Hs1'" as "Hs1".
      iDestruct (gen_heap.mapsto_agree with "Htbl1 Htbl1'") as %->.
      iModIntro. iExists _. iFrame. iNext. iIntros "[Hs1 Hs1']".
      repeat rel_pure_l.
      rel_apply_r (refines_acquire_r with "Hl2").
      iIntros "Hl2". repeat rel_pure_r.
      iDestruct (mapsto_half_combine with "Hs2 Hs2'") as "[% Hs2]"; simplify_eq.
      rel_load_r. repeat rel_pure_r.
      rel_store_r. repeat rel_pure_r.
      (* Before we close the lock, we need to gather some evidence *)
      iMod (conjure_0 γ) as "Hf".
      iMod (same_size with "[$Ha $Hf]") as "[Ha #Hf]".
      iMod (inc_size with "Ha") as "Ha".
      iDestruct "Hs2" as "[Hs2 Hs2']".
      replace (m' + 1) with (Z.of_nat (S m')); last lia.
      iMod ("Hcl" with "[Ha Hs1 Hs2 Htbl1 Htbl2]") as "_".
      { iNext. iExists _,_. by iFrame. }
      rel_load_l. repeat rel_pure_l.
      rel_store_l_atomic.
      iClear "Hls".
      iInv sizeN as (m ls) "(Ha & >Hs1 & >Hs2 & >Htbl1 & >Htbl2 & #Hls)" "Hcl".
      iDestruct (gen_heap.mapsto_agree with "Htbl1 Htbl1'") as %->.
      iCombine "Htbl1 Htbl1'" as "Htbl1".
      iModIntro. iExists _. iFrame. iNext. iIntros "[Htbl1 Htbl1']".
      repeat rel_pure_l. repeat rel_pure_r. rel_load_r.
      iDestruct (mapsto_half_combine with "Htbl2 Htbl2'") as "[% Htbl2]"; simplify_eq.
      repeat rel_pure_r. rel_store_r. repeat rel_pure_r.
      rel_apply_r (refines_release_r with "Hl2").
      iIntros "Hl2". repeat rel_pure_r.
      iDestruct "Htbl2" as "[Htbl2 Htbl2']".
      iMod ("Hcl" with "[Ha Hs1 Hs2 Htbl1 Htbl2]") as "_".
      { iNext. iExists _,_. iFrame.
        iApply lrel_list_cons; eauto. }
      rel_apply_l (refines_release_l with "Hl1 Hlk [-]"); auto.
      { iExists _,_. by iFrame. }
      iNext. do 2 rel_pure_l. rel_values.
      iExists m'. eauto.
    (* Lookup *)
    - rel_pure_l. rel_pure_r.
      iPoseProof (lookup_refinement1 with "Hinv") as "H".
      unlock. iApply "H". (* TODO how to avoid this? *)
  Qed.

  Lemma refinement2 :
    REL symbol2 << symbol1 : () → lrel_symbol.
  Proof.
    unlock symbol1 symbol2.
    iApply refines_arrow_val.
    iAlways. iIntros (? ?) "[% %]"; simplify_eq/=.
    rel_let_l. rel_let_r.
    rel_alloc_l size1 as "[Hs1 Hs1']"; repeat rel_pure_l.
    rel_alloc_r size2 as "[Hs2 Hs2']"; repeat rel_pure_r.
    rel_alloc_l tbl1 as "[Htbl1 Htbl1']"; repeat rel_pure_l.
    rel_alloc_r tbl2 as "[Htbl2 Htbl2']"; repeat rel_pure_r.
    iMod (own_alloc (● (0%nat : mnat))) as (γ) "Ha"; first done.
    iMod (inv_alloc sizeN _ (table_inv γ size1 size2 tbl1 tbl2) with "[Hs1 Hs2 Htbl1 Htbl2 Ha]") as "#Hinv".
    { iNext. iExists _,_. iFrame. iApply lrel_list_nil. }
    rel_apply_r refines_newlock_r.
    iIntros (l2) "Hl2". rel_pure_r. rel_pure_r.
    pose (N:=(relocN.@"lock1")).
    rel_apply_l (refines_newlock_l N (lok_inv size1 size2 tbl1 tbl2 l2)%I with "[Hs1' Hs2' Htbl1' Htbl2' Hl2]").
    { iExists 0%nat,_. by iFrame. }
    iNext. iIntros (l1 γl) "#Hl1". rel_pure_l. rel_pure_l.
    iApply (refines_exists (tableR γ)).
    repeat iApply refines_pair.
    (* Eq *)
    - iApply eqKey_refinement.
    (* Insert *)
    - rel_pure_l. rel_pure_r.
      iApply refines_arrow_val.
      iAlways. iIntros (? ?). iDestruct 1 as (n) "[% %]"; simplify_eq/=.
      repeat rel_pure_l. repeat rel_pure_r.
      rel_apply_l (refines_acquire_l with "Hl1").
      iNext. iIntros "Hlk Htbl". repeat rel_pure_l.
      iDestruct "Htbl" as (m ls) "(Hs1 & Hs2 & Htbl1 & Htbl2 & Hl2)".
      rel_load_l. repeat rel_pure_l.
      rel_store_l_atomic.
      iInv sizeN as (m' ls') "(Ha & >Hs1' & >Hs2' & >Htbl1' & >Htbl2' & #Hls)" "Hcl".
      iDestruct (gen_heap.mapsto_agree with "Hs1 Hs1'") as %Hm'.
      simplify_eq/=.
      iCombine "Hs1 Hs1'" as "Hs1".
      iDestruct (gen_heap.mapsto_agree with "Htbl1 Htbl1'") as %->.
      iModIntro. iExists _. iFrame. iNext. iIntros "[Hs1 Hs1']".
      repeat rel_pure_l.
      rel_apply_r (refines_acquire_r with "Hl2").
      iIntros "Hl2". repeat rel_pure_r.
      iDestruct (mapsto_half_combine with "Hs2 Hs2'") as "[% Hs2]"; simplify_eq.
      rel_load_r. repeat rel_pure_r.
      rel_store_r. repeat rel_pure_r.
      (* Before we close the lock, we need to gather some evidence *)
      iMod (conjure_0 γ) as "Hf".
      iMod (same_size with "[$Ha $Hf]") as "[Ha #Hf]".
      iMod (inc_size with "Ha") as "Ha".
      iDestruct "Hs2" as "[Hs2 Hs2']".
      replace (m' + 1) with (Z.of_nat (S m')); last lia.
      iMod ("Hcl" with "[Ha Hs1 Hs2 Htbl1 Htbl2]") as "_".
      { iNext. iExists _,_. by iFrame. }
      rel_load_l. repeat rel_pure_l.
      rel_store_l_atomic.
      iClear "Hls".
      iInv sizeN as (m ls) "(Ha & >Hs1 & >Hs2 & >Htbl1 & >Htbl2 & #Hls)" "Hcl".
      iDestruct (gen_heap.mapsto_agree with "Htbl1 Htbl1'") as %->.
      iCombine "Htbl1 Htbl1'" as "Htbl1".
      iModIntro. iExists _. iFrame. iNext. iIntros "[Htbl1 Htbl1']".
      repeat rel_pure_l. repeat rel_pure_r. rel_load_r.
      iDestruct (mapsto_half_combine with "Htbl2 Htbl2'") as "[% Htbl2]"; simplify_eq.
      repeat rel_pure_r. rel_store_r. repeat rel_pure_r.
      rel_apply_r (refines_release_r with "Hl2").
      iIntros "Hl2". repeat rel_pure_r.
      iDestruct "Htbl2" as "[Htbl2 Htbl2']".
      iMod ("Hcl" with "[Ha Hs1 Hs2 Htbl1 Htbl2]") as "_".
      { iNext. iExists _,_. iFrame.
        iApply lrel_list_cons; eauto. }
      rel_apply_l (refines_release_l with "Hl1 Hlk [-]"); auto.
      { iExists _,_. by iFrame. }
      iNext. do 2 rel_pure_l. rel_values.
      iExists m'. eauto.
    (* Lookup *)
    - rel_pure_l. rel_pure_r.
      iPoseProof (lookup_refinement2 with "Hinv") as "H".
      unlock. iApply "H". (* TODO how to avoid this? *)
  Qed.
End proof.

Definition symbolτ : type :=
  TExists (TProd (TProd (TArrow (TVar 0) (TArrow (TVar 0) TBool))
                        (TArrow TNat (TVar 0)))
                        (TArrow (TVar 0) TNat))%nat.

Theorem symbol_ctx_refinement1 :
  ∅ ⊨ symbol1 ≤ctx≤ symbol2 :
    TArrow TUnit symbolτ.
Proof.
  pose (Σ := #[relocΣ;msizeΣ;lockΣ]).
  eapply (refines_sound Σ).
  iIntros (? Δ). iApply refinement1.
Qed.

Theorem symbol_ctx_refinement2 :
  ∅ ⊨ symbol2 ≤ctx≤ symbol1 : TArrow TUnit symbolτ.
Proof.
  pose (Σ := #[relocΣ;msizeΣ;lockΣ]).
  eapply (refines_sound Σ).
  iIntros (? Δ). iApply refinement2.
Qed.
