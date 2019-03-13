(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Lists, their semantics types, and operations on them *)
From reloc Require Import proofmode.
From reloc.typing Require Import types interp.

Notation CONS h t := (SOME (Pair h t)).
Notation CONSV h t := (SOMEV (PairV h t)).
Notation NIL := NONE.
Notation NILV := NONEV.

Fixpoint is_list (hd : val) (xs : list val) : Prop :=
  match xs with
  | [] => hd = NILV
  | x :: xs => ∃ hd', hd = CONSV x hd' ∧ is_list hd' xs
  end.

(* TODO: is it possible to do this without `Program Definition`? *)
(* TODO: notation for lty_sum *)
Program Definition lty_list `{relocG Σ} (A : lty2 Σ) : lty2 Σ :=
  lty2_rec (λne B, lty2_sum () (A × B))%lty2.
Next Obligation. solve_proper. Qed.

Definition nth : val := rec: "nth" "l" "n" :=
  match: rec_unfold "l" with
    NONE      => #0
  | SOME "xs" => if: "n" = #0
                 then Fst "xs"
                 else "nth" (Snd "xs") ("n" - #1)
  end.

Lemma lty_list_nil `{relocG Σ} A :
  lty_list A NILV NILV.
Proof.
  unfold lty_list.
  rewrite lty_rec_unfold /=.
  unfold lty2_rec1 , lty2_car. (* TODO so much unfolding *)
  simpl. iNext.
  iExists _,_. iLeft. repeat iSplit; eauto.
Qed.

Lemma lty_list_cons `{relocG Σ} (A : lty2 Σ) v1 v2 ls1 ls2 :
  A v1 v2 -∗
  lty_list A ls1 ls2 -∗
  lty_list A (CONSV v1 ls1) (CONSV v2 ls2).
Proof.
  iIntros "#HA #Hls".
  rewrite {2}/lty_list lty_rec_unfold /=.
  rewrite /lty2_rec1 {3}/lty2_car.
  iNext. simpl. iExists _, _.
  iRight. repeat iSplit; eauto.
  rewrite {1}/lty2_prod /lty2_car /=.
  iExists _,_,_,_. repeat iSplit; eauto.
Qed.

Lemma refines_nth_l `{relocG Σ} (A : lty2 Σ) K v w ls (n: nat) t :
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

Lemma refines_nth_r `{relocG Σ} (A : lty2 Σ) K v w ls (n: nat) e :
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
  REL nth << nth : lty_list lty2_int → lty2_int → lty2_int.
Proof. admit. Admitted.
