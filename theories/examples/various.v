(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Modified examples from
   "The effects of higher-order state and control on local relational reasoning"
   D. Dreyer, G. Neis, L. Birkedal
*)
From iris.algebra Require Import csum agree excl.
From reloc Require Export reloc.
From reloc.lib Require Export lock counter Y.

Definition oneshotR := csumR (exclR unitR) (agreeR unitR).
Class oneshotG Σ := { oneshot_inG :> inG Σ oneshotR }.
Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
Proof. solve_inG. Qed.

Section proofs.
  Context `{relocG Σ}.

  Lemma refinement1 :
    ⊢ REL
      let: "x" := ref #1 in
      (λ: "f", "f" #();; !"x")
    <<
      (λ: "f", "f" #();; #1)
    : (() → ()) → lrel_int.
  Proof.
    rel_alloc_l x as "Hx".
    repeat rel_pure_l.
    iMod (inv_alloc (nroot.@"xinv") _ (x ↦ #1)%I with "Hx") as "#Hinv".
    rel_pure_r. iApply refines_arrow.
    iAlways. iIntros (f1 f2) "#Hff".
    rel_rec_l. rel_rec_r.
    iApply (refines_seq with "[Hff]").
    - iApply refines_app; eauto.
      rel_values; eauto.
    - rel_load_l_atomic.
      iInv (nroot.@"xinv") as "Hx" "Hcl".
      iModIntro. iExists _; iFrame "Hx"; simpl.
      iNext. iIntros "Hx".
      iMod ("Hcl" with "Hx") as "_".
      rel_values.
  Qed.

  Definition pending γ `{oneshotG Σ} := own γ (Cinl (Excl ())).
  Definition shot γ `{oneshotG Σ} := own γ (Cinr (to_agree ())).
  Lemma new_pending `{oneshotG Σ} : ⊢ |==> ∃ γ, pending γ.
  Proof. by apply own_alloc. Qed.
  Lemma shoot γ `{oneshotG Σ} : pending γ ==∗ shot γ.
  Proof.
    apply own_update.
    intros n [f |]; simpl; eauto.
    destruct f; simpl; try by inversion 1.
  Qed.
  Definition shootN := nroot .@ "shootN".
  Lemma shot_not_pending γ `{oneshotG Σ} :
    shot γ -∗ pending γ -∗ False.
  Proof.
    iIntros "Hs Hp".
    iPoseProof (own_valid_2 with "Hs Hp") as "H".
    iDestruct "H" as %[].
  Qed.

  Lemma refinement2 `{oneshotG Σ} :
    ⊢ REL
      let: "x" := ref #0 in
      (λ: "f", "x" <- #1;; "f" #();; !"x")
    <<
      (let: "x" := ref #1 in
       λ: "f", "f" #();; !"x")
    : (() → ()) → lrel_int.
  Proof.
    rel_alloc_l x as "Hx".
    rel_alloc_r y as "Hy".
    repeat rel_pure_l; repeat rel_pure_r.
    iMod new_pending as (γ) "Ht".
    iMod (inv_alloc shootN _ ((x ↦ #0 ∗ pending γ ∨ x ↦ #1 ∗ shot γ) ∗ y ↦ₛ #1)%I with "[Hx Ht $Hy]") as "#Hinv".
    { iNext. iLeft. iFrame. }
    iApply refines_arrow.
    iIntros "!#" (f1 f2) "#Hf".
    rel_let_l. rel_let_r.
    rel_store_l_atomic.
    iInv shootN as "[[[Hx Hp] | [Hx #Hs]] Hy]" "Hcl";
      iModIntro; iExists _; iFrame "Hx"; iNext; iIntros "Hx"; repeat rel_pure_l.
    - iMod (shoot γ with "Hp") as "#Hs".
      iMod ("Hcl" with "[$Hy Hx]") as "_".
      { iNext. iRight. by iFrame. }
      iApply (refines_seq with "[Hf]").
      + iApply (refines_app with "Hf").
        by rel_values.
      + rel_load_l_atomic.
        iInv shootN as "[[[Hx >Hp] | [Hx Hs']] Hy]" "Hcl".
        { iExFalso. iApply (shot_not_pending with "Hs Hp"). }
        iModIntro. iExists _; iFrame. iNext. simpl.
        iIntros "Hx".
        rel_load_r.
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iFrame. iRight; by iFrame. }
        rel_values.
    - iMod ("Hcl" with "[$Hy Hx]") as "_".
      { iNext. iRight. by iFrame. }
      iApply (refines_seq with "[Hf]"); auto.
      + iApply (refines_app with "Hf").
        by rel_values.
      + rel_load_l_atomic.
        iInv shootN as "[[[Hx >Hp] | [Hx Hs']] Hy]" "Hcl".
        { iExFalso. iApply (shot_not_pending with "Hs Hp"). }
        iModIntro. iExists _; iFrame. iNext.
        iIntros "Hx".
        rel_load_r.
        iMod ("Hcl" with "[-]").
        { iNext. iFrame. iRight; by iFrame. }
        rel_values.
  Qed.

  Lemma refinement25 `{oneshotG Σ} :
    ⊢ REL
      (λ: "f", "f" #();; #1)
    <<
      (let: "x" := ref #0 in
       (λ: "f", "x" <- #1;; "f" #();; !"x"))
    : (() → ()) → lrel_int.
  Proof.
    rel_alloc_r x as "Hx".
    repeat rel_pure_r.
    iMod new_pending as (γ) "Ht".
    iMod (inv_alloc shootN _ ((x ↦ₛ #0 ∗ pending γ ∨ x ↦ₛ #1 ∗ shot γ))%I with "[Hx Ht]") as "#Hinv".
    { iNext. iLeft. iFrame. }
    rel_pure_l.
    iApply refines_arrow.
    iIntros "!#" (f1 f2) "#Hf".
    repeat rel_pure_l. repeat rel_pure_r.
    iInv shootN as ">[[Hx Hp] | [Hx #Hs]]" "Hcl";
      rel_store_r; repeat rel_pure_r.
    - iMod (shoot γ with "Hp") as "#Hs".
      iMod ("Hcl" with "[Hx]") as "_".
      { iNext. iRight. by iFrame. }
      iApply (refines_seq with "[Hf]"); auto.
      + iApply (refines_app with "Hf").
        rel_values.
      + iInv shootN as "[[>Hx >Hp] | [>Hx _]]" "Hcl";
          rel_load_r.
        { iExFalso. iApply (shot_not_pending with "Hs Hp"). }
        iMod ("Hcl" with "[Hx]") as "_".
        { iNext. iRight. by iFrame. }
        rel_values.
    - iMod ("Hcl" with "[Hx]") as "_".
      { iNext. iRight. by iFrame. }
      iApply (refines_seq with "[Hf]"); auto.
      + iApply (refines_app with "Hf").
        rel_values.
      + iInv shootN as "[[>Hx >Hp] | [>Hx _]]" "Hcl";
          rel_load_r.
        { iExFalso. iApply (shot_not_pending with "Hs Hp"). }
        iMod ("Hcl" with "[Hx]") as "_".
        { iNext. iRight. by iFrame. }
        rel_values.
  Qed.

  (** A "callback with lock" example *)
  Definition i3 (x x' b b' : loc) : iProp Σ :=
    (∃ (n:nat), x ↦{1/2} #n ∗ x' ↦ₛ{1/2} #n ∗
    ((b ↦ #true ∗ b' ↦ₛ #true ∗ x ↦{1/2} #n ∗ x' ↦ₛ{1/2} #n)
    ∨ (b ↦ #false ∗ b' ↦ₛ #false)))%I.
  Definition i3n := nroot .@ "i3".

  Lemma refinement3 :
    ⊢ REL
      let: "b" := ref #true in
      let: "x" := ref #0 in
      (λ: "f", if: CAS "b" #true #false
               then "f" #();; "x" <- !"x" + #1 ;; "b" <- #true
               else #(),
       λ: <>, !"x")
    <<
      (let: "b" := ref #true in
      let: "x" := ref #0 in
      (λ: "f", if: CAS "b" #true #false
               then let: "n" := !"x" in
                    "f" #();; "x" <- "n" + #1 ;; "b" <- #true
               else #(),
       λ: <>, !"x"))
    : ((() → ()) → ()) * (() → lrel_int).
  Proof.
    rel_alloc_l b as "Hb".
    repeat rel_pure_l.
    rel_alloc_l x as "Hx".
    rel_pure_l. rel_pure_l.
    rel_alloc_r b' as "Hb'".
    repeat rel_pure_r.
    rel_alloc_r x' as "Hx'".
    rel_pure_r. rel_pure_r.
    iMod (inv_alloc i3n _ (i3 x x' b b') with "[-]") as "#Hinv".
    { iNext. unfold i3. iExists 0.
      iDestruct "Hx" as "[$ Hx]".
      iDestruct "Hx'" as "[$ Hx']".
      iLeft. iFrame. }
    iApply refines_pair.
    - rel_pure_l. rel_pure_r.
      iApply refines_arrow.
      iAlways. iIntros (f f') "Hf".
      rel_let_l. rel_let_r.
      rel_cmpxchg_l_atomic.
      iInv i3n as (n) "(Hx & Hx' & >Hbb)" "Hcl".
      iDestruct "Hbb" as "[(Hb & Hb' & Hx1 & Hx'1) | (Hb & Hb')]"; last first.
      { iModIntro; iExists _; iFrame. simpl.
        iSplitL; last by iIntros (?); congruence.
        iIntros (?); iNext; iIntros "Hb".
        rel_cmpxchg_fail_r; rel_pures_r; rel_pures_l.
        iMod ("Hcl" with "[-]").
        { iNext. iExists n. iFrame. iRight. iFrame. }
        rel_values. }
      { iModIntro. iExists _; iFrame. simpl.
        iSplitR; first by iIntros (?); congruence.
        iIntros (?); iNext; iIntros "Hb".
        rel_cmpxchg_suc_r; rel_pures_r; rel_pures_l.
        rel_load_r. repeat rel_pure_r.
        iMod ("Hcl" with "[Hb Hb' Hx Hx']") as "_".
        { iNext. iExists _; iFrame. iRight. iFrame. }
        iApply (refines_seq with "[Hf]"); auto.
        { iApply (refines_app with "Hf").
          rel_values. }
        rel_load_l. rel_pure_l. rel_pure_r.
        rel_store_l_atomic.
        iInv i3n as (n') "(>Hx & Hx' & >Hbb)" "Hcl".
        iDestruct (mapsto_agree with "Hx Hx1") as %->.
        iCombine "Hx Hx1" as "Hx".
        iModIntro. iExists _; iFrame. iNext.
        iIntros "Hx".
        iCombine "Hx' Hx'1" as "Hx'".
        rel_store_r.
        iDestruct "Hx" as "[Hx Hx1]".
        iDestruct "Hx'" as "[Hx' Hx'1]".
        iDestruct "Hbb" as "[(Hb & Hb' & Hx2 & Hx'2) | Hbb]".
        { iCombine "Hx Hx1" as "Hx".
          iDestruct (mapsto_valid_2 with "Hx Hx2") as %Hfoo. exfalso.
          compute in Hfoo. eauto. }
        iMod ("Hcl" with "[Hx Hx' Hbb]") as "_".
        { iNext. iExists (S n).
          replace (Z.of_nat (S n)) with (n + 1)%Z by lia.
          iFrame. }
        repeat rel_pure_l. repeat rel_pure_r.
        rel_store_l_atomic. clear n'.
        iInv i3n as (n') "(>Hx & Hx' & >Hbb)" "Hcl".
        iDestruct (mapsto_agree with "Hx Hx1") as %->.
        iDestruct "Hbb" as "[(Hb & Hb' & Hx2 & Hx'2) | (Hb & Hb')]".
        { iCombine "Hx Hx1" as "Hx".
          iDestruct (mapsto_valid_2 with "Hx Hx2") as %Hfoo. exfalso.
          compute in Hfoo. eauto. }
        iModIntro; iExists _; iFrame; iNext. iIntros "Hb".
        rel_store_r.
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists (S n).
          replace (Z.of_nat (S n)) with (n + 1)%Z by lia.
          iFrame. iLeft. iFrame. }
        rel_values. }
    - rel_pure_l. rel_pure_r. iApply refines_arrow.
      iAlways. iIntros (u u') "_".
      rel_let_l. rel_let_r.
      rel_load_l_atomic.
      iInv i3n as (n) "(>Hx & Hx' & >Hbb)" "Hcl".
      iModIntro. iExists _; iFrame; iNext. iIntros "Hx".
      rel_load_r.
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _. iFrame. }
      rel_values.
  Qed.

  (** /Sort of/ a well-bracketedness example.
      Without locking in the first expression, the callback can reenter
      the body in a forked thread to change the value of x *)
  Lemma refinement4 `{!lockG Σ}:
    ⊢ REL
      (let: "x" := ref #1 in
       let: "l" := newlock #() in
       λ: "f", acquire "l";;
               "x" <- #0;; "f" #();;
               "x" <- #1;; "f" #();;
               let: "v" := !"x" in
               release "l";; "v")
    <<
      (let: "x" := ref #0 in
       λ: "f", "f" #();; "x" <- #1;; "f" #();; !"x")
    : (() → ()) → lrel_int.
  Proof.
    rel_alloc_l x as "Hx".
    rel_alloc_r y as "Hy".
    repeat rel_pure_l; repeat rel_pure_r.
    pose (N:=relocN.@"lock").
    rel_apply_l (refines_newlock_l N (∃ (n m : Z), x ↦ #n ∗ y ↦ₛ #m)%I with "[Hx Hy]").
    { iExists 1, 0. iFrame. }
    iNext. iIntros (l γ) "#Hl".
    repeat rel_pure_l.
    iApply refines_arrow; auto.
    iIntros "!#" (f1 f2) "#Hf".
    rel_let_l. rel_let_r.
    rel_apply_l (refines_acquire_l N _ l with "Hl").
    iNext. iIntros "Hlocked". iDestruct 1 as (n m) "[Hx Hy]".
    repeat rel_pure_l. rel_store_l. repeat rel_pure_l.
    iApply (refines_seq () with "[Hf]").
    { iApply (refines_app with "Hf").
      rel_values. }
    rel_store_l. repeat rel_pure_l.
    rel_store_r. repeat rel_pure_r.
    iApply (refines_seq () with "[Hf]").
    { iApply (refines_app with "Hf").
      rel_values. }
    rel_load_l. repeat rel_pure_l.
    rel_load_r. repeat rel_pure_r.
    rel_apply_l (refines_release_l N _ l γ with "Hl Hlocked [Hx Hy]"); eauto.
    { iExists _,_. iFrame. }
    iNext. repeat rel_pure_l.
    rel_values.
  Qed.

  (** "Single return" example *)
  Lemma refinement5 :
    ⊢ REL
      (λ: "f", let: "x" := ref #0 in
               let: "y" := ref #0 in
               "f" #();;
               "x" <- !"y";;
               "y" <- #1;;
               !"x")
    <<
      (λ: "f", let: "x" := ref #0 in
               let: "y" := ref #0 in
               "f" #();;
               "x" <- !"y";;
               "y" <- #2;;
               !"x")
    : (() → ()) → lrel_int.
  Proof.
    rel_pure_l. rel_pure_r. iApply refines_arrow; eauto.
    iAlways. iIntros (f1 f2) "Hf".
    rel_let_l. rel_let_r.
    rel_alloc_l x as "Hx". repeat rel_pure_l.
    rel_alloc_l y as "Hy". repeat rel_pure_l.
    rel_alloc_r x' as "Hx'". repeat rel_pure_r.
    rel_alloc_r y' as "Hy'". repeat rel_pure_r.
    iApply (refines_seq with "[Hf]"); eauto.
    { iApply (refines_app with "Hf").
      rel_values. }
    rel_load_l. rel_load_r.
    rel_store_l. rel_store_r.
    repeat rel_pure_l. repeat rel_pure_r.
    rel_store_l. rel_store_r.
    repeat rel_pure_l. repeat rel_pure_r.
    rel_load_l. rel_load_r.
    rel_values.
  Qed.

  (** Higher-order profiling *)
  Definition τg := TArrow TUnit TUnit.
  Definition τf := TArrow τg TUnit.
  Definition p : val := λ: "g", let: "c" := ref #0 in
                                (λ: <>, FG_increment "c";; "g" #(), λ: <>, !"c").
  (** The idea for the invariant is that we have to states:
       a) c1 = n, c2 = n
       b) c1 = n+1, c2 = n
      We start in state (a) and can only transition to the state (b) by giving away an exclusive token.
      But once we have transitioned to (b), we remain there forever.
      To that extent we use to resources algebras two model two of those conditions, and we tie it all together in the invariant.
  *)
  Definition i6 `{oneshotG Σ} `{inG Σ (exclR unitR)} (c1 c2 : loc) γ γ' :=
    (∃ (n : nat),
     (c1 ↦ #n ∗ c2 ↦ₛ #n ∗ pending γ)
   ∨ (c1 ↦ #(n+1) ∗ c2 ↦ₛ #n ∗ shot γ ∗ own γ' (Excl ())))%I.

  Lemma profiled_g `{oneshotG Σ} `{inG Σ (exclR unitR)} γ γ' c1 c2 g1 g2 :
    inv shootN (i6 c1 c2 γ γ') -∗
    □ (REL g1 << g2 : () → ()) -∗
    REL
      (FG_increment #c1;; g1 #())
    <<
      (FG_increment #c2;; g2 #()) : ().
  Proof.
    iIntros "#Hinv #Hg".
    iApply (refines_seq lrel_true); last first.
    { iApply (refines_app with "Hg").  rel_values. }
    rel_apply_l (FG_increment_atomic_l
      (fun (n : nat) => (c2 ↦ₛ #n ∗ pending γ) ∨ (c2 ↦ₛ #(n-1) ∗ shot γ ∗ own γ' (Excl ()) ∗ ⌜1 ≤ n⌝))%I True%I); first done.
    iAlways.
    iInv shootN as (n) ">[(Hc1 & Hc2 & Ht) | (Hc1 & Hc2 & Ht)]" "Hcl".
      iModIntro.
    - iExists n. iFrame "Hc1".  iSplitL "Hc2 Ht".
      { iLeft. iFrame. }
      iSplit.
      { iIntros "[Hc1 [(Hc2 & Ht) | (Hc2 & Ht & Ht' & %)]]";
        iApply ("Hcl" with "[-]"); iNext.
        + iExists n. iLeft. iFrame.
        + iExists (n-1). iRight.
          replace (Z.of_nat (n - 1)) with (Z.of_nat n - 1)%Z by lia.
          replace (n - 1 + 1)%Z with (Z.of_nat n) by lia.
         iFrame. }
      { iIntros "[Hc1 Hc] _".
        iDestruct "Hc" as "[[Hc2 Ht] | [Hc2 [Ht [Ht' %]]]]".
        - rel_apply_r (FG_increment_r with "Hc2"). iIntros "Hc2".
          iMod ("Hcl" with "[-]") as "_".
          { iNext. iExists (n + 1).
            replace (Z.of_nat (n + 1)) with (Z.of_nat n + 1)%Z by lia.
            iLeft; iFrame. }
          rel_values.
        - replace (Z.of_nat n - 1)%Z with (Z.of_nat (n - 1)) by lia.
          rel_apply_r (FG_increment_r with "Hc2"). iIntros "Hc2".
          iMod ("Hcl" with "[-]") as "_".
          { iNext. iExists n. iRight; iFrame.
            by replace ((n - 1)%nat + 1)%Z with (Z.of_nat n) by lia. }
         rel_values. }
    - iModIntro. iExists (n + 1).
      replace (Z.of_nat n + 1)%Z with (Z.of_nat (n + 1)) by lia. iFrame.
      iSplitL "Hc2 Ht".
      { iRight. replace ((n + 1)%nat - 1)%Z with (Z.of_nat n) by lia.
        iFrame. iDestruct "Ht" as "[$ $]".
        iPureIntro. lia. }
      iSplit.
      { iIntros "[Hc1 [(Hc2 & Ht) | (Hc2 & Ht & Ht' & %)]]";
        iApply ("Hcl" with "[-]"); iNext.
        + iExists (S n). iLeft.
          replace (Z.of_nat (n + 1)) with (Z.of_nat (S n)) by lia. iFrame.
        + iExists n. iRight. iFrame.
          replace (Z.of_nat (n + 1)) with (Z.of_nat n + 1)%Z by lia.
          replace (n + 1 - 1)%Z with (Z.of_nat n) by lia.
          iFrame. }
     { iIntros "[Hc1 Hc] _".
        iDestruct "Hc" as "[[Hc2 Ht] | [Hc2 [Ht [Ht' %]]]]".
        - rel_apply_r (FG_increment_r with "Hc2").
          iIntros "Hc2".
          iMod ("Hcl" with "[-]") as "_".
          { iNext. iExists (S (S n)).
            replace ((n+1)%nat + 1)%Z with (Z.of_nat (S (S n))) by lia.
            iLeft; iFrame. }
          rel_values.
        - replace ((n + 1)%nat + 1)%Z with (Z.of_nat (S n) + 1)%Z by lia.
          replace ((n + 1)%nat - 1)%Z with (Z.of_nat n) by lia.
          rel_apply_r (FG_increment_r with "Hc2").
          iIntros "Hc2".
          iMod ("Hcl" with "[-]") as "_".
          { iNext. iExists (S n). iRight. iFrame.
            by replace (n + 1)%Z with (Z.of_nat (S n)) by lia. }
          rel_values. }
  Qed.

  Lemma profiled_g' `{oneshotG Σ} `{inG Σ (exclR unitR)} γ γ' c1 c2 g1 g2 :
    inv shootN (i6 c1 c2 γ γ') -∗
    □ (REL g1 << g2 : () → ()) -∗
    REL
      (λ: <>, FG_increment #c1;; g1 #())%V
    <<
      (λ: <>, FG_increment #c2;; g2 #())%V : () → ().
  Proof.
    iIntros "#Hinv #Hg".
    iApply refines_arrow_val; auto.
    iAlways. iIntros (? ?) "[% %]". simplify_eq/=.
    rel_seq_l. rel_seq_r.
    iApply profiled_g; eauto.
  Qed.

  Lemma close_i6 c1 c2 γ γ' `{oneshotG Σ} `{inG Σ (exclR unitR)} :
    (∃ n : nat, c1 ↦ #n
     ∗ (c2 ↦ₛ #n ∗ pending γ
       ∨ c2 ↦ₛ #(n - 1) ∗ shot γ ∗ own γ' (Excl ()) ∗ ⌜1 ≤ n⌝))
     -∗ i6 c1 c2 γ γ'.
  Proof.
    iDestruct 1 as (m) "[Hc1 Hc2]".
    iDestruct "Hc2" as "[[Hc2 Hp] | (Hc2 & Hs & Ht & %)]";
      [iExists m; iLeft | iExists (m - 1); iRight]; iFrame.
    replace ((m - 1)%nat + 1)%Z with (Z.of_nat m) by lia.
    replace (Z.of_nat (m - 1)) with (Z.of_nat m - 1)%Z by lia.
    iFrame.
  Qed.

  Lemma refinement6_helper f'1 f'2 g1 g2 c1 c2 γ γ' m `{oneshotG Σ} `{inG Σ (exclR unitR)} :
    inv shootN (i6 c1 c2 γ γ') -∗
    □ (REL g1 << g2 : () → ()) -∗
    □ (REL f'1 << f'2 : (() → ()) → ()) -∗
    (▷ i6 c1 c2 γ γ' ={⊤ ∖ ↑shootN,⊤}=∗ True) -∗
    c1 ↦ #(S m) -∗
    (c2 ↦ₛ #m ∗ pending γ
      ∨ c2 ↦ₛ #(m - 1) ∗ shot γ ∗ own γ' (Excl ()) ∗ ⌜1 ≤ m⌝) -∗
    own γ' (Excl ()) -∗
    REL (g1 #();; f'1 (λ: <>, FG_increment #c1;; g1 #())%V;; (λ: <>, ! #c1)%V #())
      <<
        (g2 #();; f'2 (λ: <>, FG_increment #c2;; g2 #())%V;; (λ: <>, ! #c2)%V #() + #1)
      @ ⊤ ∖ ↑shootN : lrel_int.
  Proof.
    iIntros "#Hinv #Hg #Hf Hcl Hc1 Hc2 Ht".
    iDestruct "Hc2" as "[(Hc2 & Hp) | (Hc2 & Hs & Ht'2 & %)]"; last first.
    { iDestruct (own_valid_2 with "Ht Ht'2") as %Hfoo.
      inversion Hfoo. }
    iMod (shoot γ with "Hp") as "#Hs".
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists m. iRight. iFrame.
      replace (Z.of_nat (S m)) with (Z.of_nat m + 1)%Z by lia. by iFrame. }
    iApply (refines_seq lrel_unit).
    { iApply (refines_app with "Hg").
      rel_values. }
    iApply (refines_seq lrel_unit).
    { iApply (refines_app with "Hf").
      by iApply profiled_g'. }
    repeat rel_pure_l. repeat rel_pure_r.
    rel_load_l_atomic. clear m.
    iInv shootN as (m) ">[(Hc1 & Hc2 & Ht) | (Hc1 & Hc2 & Ht & Ht')]" "Hcl";
      iModIntro; iExists _; iFrame.
    { iExFalso. by iApply shot_not_pending. }
    iNext. iIntros "Hc1".
    rel_load_r. rel_op_r.
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists m. iRight. iFrame. }
    rel_values.
  Qed.

  Lemma refinement6 `{oneshotG Σ} `{inG Σ (exclR unitR)} :
    ⊢ REL
      (λ: "f" "g" "f'",
       let: "pg" := p "g" in
       let: "g'" := Fst "pg" in
       let: "g''" := Snd "pg" in
       "f" "g'";; "g'" #();; "f'" "g'";; "g''" #())
    <<
      (λ: "f" "g" "f'",
       let: "pg" := p "g" in
       let: "g'" := Fst "pg" in
       let: "g''" := Snd "pg" in
       "f" "g'";; "g" #();; "f'" "g'";; "g''" #() + #1)
    : ((() → ()) → ()) → (() → ()) → ((() → ()) → ()) → lrel_int.
  Proof.
    rel_pure_l. rel_pure_r.
    iApply refines_arrow.
    iIntros "!#" (f1 f2) "#Hf".
    repeat rel_pure_l. repeat rel_pure_r.
    iApply refines_arrow.
    iIntros "!#" (g1 g2) "#Hg".
    repeat rel_pure_l. repeat rel_pure_r.
    iApply refines_arrow.
    iIntros "!#" (f'1 f'2) "#Hf'".
    repeat rel_pure_l. repeat rel_pure_r.
    rel_rec_l. rel_rec_r.
    rel_alloc_l c1 as "Hc1".
    rel_alloc_r c2 as "Hc2".
    iMod new_pending as (γ) "Ht".
    iMod (own_alloc (Excl ())) as (γ') "Ht'"; first done.
    iMod (inv_alloc shootN _ (i6 c1 c2 γ γ') with "[Hc1 Hc2 Ht]") as "#Hinv".
    { iNext. iExists 0. iLeft. iFrame. }
    repeat rel_pure_l. repeat rel_pure_r.
    iApply (refines_seq lrel_unit).
    { iApply (refines_app with "Hf").
      by iApply profiled_g'. }
    rel_seq_l.
    rel_apply_l (FG_increment_atomic_l
      (fun (n : nat) => (c2 ↦ₛ #n ∗ pending γ) ∨ (c2 ↦ₛ #(n-1) ∗ shot γ ∗ own γ' (Excl ()) ∗ ⌜1 ≤ n⌝))%I with "Ht'").
    iAlways.
    iInv shootN as (n) ">[(Hc1 & Hc2 & Ht) | (Hc1 & Hc2 & Ht & Ht'2)]" "Hcl";
      iModIntro; last first.
    { iExists (S n). replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
      iFrame. iSplitL "Hc2 Ht Ht'2".
      { iRight. simpl. replace (n + 1 - 1)%Z with (Z.of_nat n) by lia.
        iFrame. iPureIntro. lia. }
      iSplit.
      - iIntros. iApply "Hcl". iApply close_i6.
        iNext. iExists (S n). replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
        iFrame.
      - iIntros "[Hc1 Hc2] Ht".
        rel_pure_l. rel_pure_l.
        replace (n + 1 + 1)%Z with (Z.of_nat (S (S n))) by lia.
        replace (n + 1)%Z with (Z.of_nat (S n)) by lia.
        iApply (refinement6_helper with "Hinv Hg Hf' Hcl Hc1 Hc2 Ht").
    }
    { iExists n. iFrame "Hc1". iSplitL "Hc2 Ht".
      { iLeft. by iFrame. }
      iSplit.
      - iIntros. iApply "Hcl". iApply close_i6.
        iNext. iExists _; iFrame.
      - iIntros  "[Hc1 Hc2] Ht".
        rel_pure_l. rel_pure_l.
        replace (n + 1)%Z with (Z.of_nat (S n)) by lia.
        iApply (refinement6_helper with "Hinv Hg Hf' Hcl Hc1 Hc2 Ht").
    }
  Qed.

End proofs.
