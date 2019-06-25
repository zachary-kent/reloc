(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Lists, their semantics types, and operations on them *)
From reloc Require Import reloc.
Set Default Proof Using "Type".

Notation CONS h t := (SOME (Pair h t)).
Notation CONSV h t := (SOMEV (PairV h t)).
Notation NIL := NONE.
Notation NILV := NONEV.

Fixpoint is_list (hd : val) (xs : list val) : Prop :=
  match xs with
  | [] => hd = NILV
  | x :: xs => ∃ hd', hd = CONSV x hd' ∧ is_list hd' xs
  end.

Program Definition lrel_list `{relocG Σ} (A : lrel Σ) : lrel Σ :=
  lrel_rec (λne B, () + (A * B))%lrel.
Next Obligation. solve_proper. Qed.

Definition nth : val := rec: "nth" "l" "n" :=
  match: rec_unfold "l" with
    NONE      => #0
  | SOME "xs" => if: "n" = #0
                 then Fst "xs"
                 else "nth" (Snd "xs") ("n" - #1)
  end.

Lemma lrel_list_unfold `{relocG Σ} A v1 v2:
  lrel_list A v1 v2 ≡
   (▷ ((⌜v1 = NILV⌝ ∧ ⌜v2 = NILV⌝)
      ∨ (∃ w1 w2 t1 t2, ⌜v1 = CONSV w1 t1⌝ ∧
                        ⌜v2 = CONSV w2 t2⌝ ∗
                        A w1 w2 ∗ lrel_list A t1 t2)))%I.
Proof.
  rewrite /lrel_list.
  rewrite {1}lrel_rec_unfold /=.
  unfold lrel_rec1, lrel_car. (* TODO: so much unfolding *)
  simpl. iSplit.
  - iIntros "H". iNext.
    iDestruct "H" as (w1 w2) "H".
    iDestruct "H" as "[(->&->&H)|(->&->&H)]".
    + iLeft. iDestruct "H" as "[-> ->]". done.
    + iRight. iDestruct "H" as (????->->) "[??]".
      iExists _,_,_,_. repeat iSplit; eauto.
  - iIntros "H". iNext.
    iDestruct "H" as "[[-> ->]|H]".
    + iExists #(),#(). iLeft. eauto with iFrame.
    + iDestruct "H" as (????->->) "[??]".
      iExists (_,_)%V,(_,_)%V. iRight.
      repeat iSplit; eauto with iFrame.
      iExists _,_,_,_. repeat iSplit; eauto with iFrame.
Qed.

Lemma lrel_list_nil `{relocG Σ} A :
  lrel_list A NILV NILV.
Proof.
  rewrite lrel_list_unfold.
  iNext. by iLeft.
Qed.

Lemma lrel_list_cons `{relocG Σ} (A : lrel Σ) v1 v2 ls1 ls2 :
  ▷ A v1 v2 -∗
  ▷ lrel_list A ls1 ls2 -∗
  lrel_list A (CONSV v1 ls1) (CONSV v2 ls2).
Proof.
  iIntros "#HA #Hls".
  rewrite (lrel_list_unfold A (CONSV _ _)).
  iNext. iRight. iExists _,_,_,_. eauto with iFrame.
Qed.

Lemma refines_nth_l `{relocG Σ} (A : lrel Σ) K v w ls (n: nat) t :
  is_list v ls →
  ls !! n = Some w →
  (REL fill K (of_val w) << t : A) -∗
  REL fill K (nth v #n) << t : A.
Proof.
  iInduction ls as [|hd tl] "IH" forall (v n).
  - iIntros (_ Hl). destruct n; simplify_eq/=.
  - iIntros (Hv Hn) "Hl". simpl in *.
    destruct Hv as (hd' & -> & Hv).
    rel_rec_l. repeat rel_pure_l.
    rel_rec_l. repeat rel_pure_l.
    destruct n as [|n'].
    + rewrite bool_decide_true //.
      repeat rel_pure_l. simpl in Hn.
      by simplify_eq/=.
    + rewrite bool_decide_false //.
      repeat rel_pure_l. simpl in Hn.
      replace ((S n')%nat - 1)%Z with (Z.of_nat n'); last by lia.
      iApply "IH"; eauto.
Qed.

Lemma refines_nth_r `{relocG Σ} (A : lrel Σ) K v w ls (n: nat) e :
  is_list v ls →
  ls !! n = Some w →
  (REL e << fill K (of_val w) : A) -∗
  REL e << fill K (nth v #n) : A.
Proof.
  iInduction ls as [|hd tl] "IH" forall (v n).
  - iIntros (_ Hl). destruct n; simplify_eq/=.
  - iIntros (Hv Hn) "Hl". simpl in *.
    destruct Hv as (hd' & -> & Hv).
    rel_rec_r. repeat rel_pure_r.
    rel_rec_r. repeat rel_pure_r.
    destruct n as [|n'].
    + rewrite bool_decide_true //.
      repeat rel_pure_r. simpl in Hn.
      by simplify_eq/=.
    + rewrite bool_decide_false //.
      repeat rel_pure_r. simpl in Hn.
      replace ((S n')%nat - 1)%Z with (Z.of_nat n'); last by lia.
      iApply "IH"; eauto.
Qed.

Lemma nth_int_typed `{relocG Σ} :
  REL nth << nth : lrel_list lrel_int → lrel_int → lrel_int.
(* XXX derive this from the fundamental property *)
Proof.
  unfold nth.
  rel_arrow_val. fold nth.
  iIntros (l1 l2) "#Hl".
  rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r.
  rel_arrow_val. iIntros (n1 n2) "Hn".
  iRevert "Hl". iIntros "Hl".
  rel_rec_l. rel_rec_r.
  iLöb as "IH" forall (l1 l2 n1 n2).
  iDestruct "Hl" as "#Hl".
  rewrite /rec_unfold lrel_list_unfold.
  rel_pures_l. rel_pures_r.
  iDestruct "Hl" as "[[-> ->]|Hl]"; rel_pures_l; rel_pures_r.
  - rel_values.
  - iDestruct "Hl" as (w1 w2 t1 t2 -> ->) "[Hw Hl]".
    rel_pures_l. rel_pures_r.
    iDestruct "Hn" as (n) "[-> ->]".
    case_bool_decide; rel_pures_l; rel_pures_r.
    + rel_values.
    + rel_rec_l. rel_rec_r.
      rel_pures_l. rel_pures_r.
      iApply ("IH" with "[] Hl").
      iExists (n-1)%Z. eauto with iFrame.
Qed.
