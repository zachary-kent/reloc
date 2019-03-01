(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Tactics and lemmas for properness and non-expansiveness. *)
From stdpp Require Export tactics.
From iris.algebra Require Export ofe gmap.
From iris.base_logic Require Export base_logic lib.invariants.
From iris.program_logic Require Import weakestpre.
Import uPred.

(* Hmmm *)
Ltac my_prepare :=
  intros;
  repeat lazymatch goal with
  | |- Proper _ _ => intros ???
  | |- (_ ==> _)%signature _ _ => intros ???
  | |- pointwise_relation _ _ _ _ => intros ?
  end; simplify_eq.

Ltac solve_proper_from_ne :=
  my_prepare;
  solve [repeat first [done | eassumption | apply equiv_dist=>? |
    match goal with
    | [H : _ ≡ _ |- _] => setoid_rewrite equiv_dist in H; rewrite H
    end] ].

Ltac properness :=
  repeat match goal with
  | |- (∃ _: _, _)%I ≡ (∃ _: _, _)%I => apply exist_proper =>?
  | |- (∀ _: _, _)%I ≡ (∀ _: _, _)%I => apply forall_proper =>?
  | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply and_proper
  | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply or_proper
  | |- (_ → _)%I ≡ (_ → _)%I => apply impl_proper
  | |- (_ -∗ _)%I ≡ (_ -∗ _)%I => apply wand_proper
  | |- (WP _ @ _ {{ _ }})%I ≡ (WP _ @ _ {{ _ }})%I => apply wp_proper =>?
  | |- (▷ _)%I ≡ (▷ _)%I => apply later_proper
  | |- (□ _)%I ≡ (□ _)%I => apply intuitionistically_proper
  | |- (|={_,_}=> _ )%I ≡ (|={_,_}=> _ )%I => apply fupd_proper
  | |- (_ ∗ _)%I ≡ (_ ∗ _)%I => apply sep_proper
  | |- (inv _ _)%I ≡ (inv _ _)%I => apply (contractive_proper _)
  end.

Section big_opm.
  Context `{Countable K} {A : ofeT}.
  Context `{Monoid M o}.

  Infix "`o`" := o (at level 50, left associativity).
  Implicit Types m : gmap K A.
  Implicit Types f g : K → A → M.

  Global Instance big_opM_ne2 n `{Proper _ (dist n ==> dist n ==> dist n) o} :
    Proper (pointwise_relation _ (dist n ==> dist n) ==> dist n ==> dist n)
           (big_opM o (K:=K) (A:=A)).
  Proof.
    intros f g Hf m1.
    induction m1 as [|i x m Hnone IH] using map_ind.
    { intros m2 Hm2. rewrite big_opM_empty.
      induction m2 as [|j y m2 ? IH2] using map_ind.
      - by rewrite big_opM_empty.
      - exfalso.
        specialize (Hm2 j). revert Hm2.
        rewrite lookup_insert lookup_empty /=. by inversion 1. }
    intros m2 Hm2.
    assert (is_Some (m2 !! i)) as [y Hy].
    { specialize (Hm2 i). revert Hm2. rewrite lookup_insert=>Hm2.
      destruct (m2 !! i); first naive_solver.
      inversion Hm2. }
    replace m2 with (<[i:=y]>(delete i m2)).
    - rewrite !big_opM_insert // /=; last by apply lookup_delete.
      f_equiv.
      + apply Hf. specialize (Hm2 i). revert Hm2.
        rewrite Hy lookup_insert //. by inversion 1.
      + apply IH=> j.
        destruct (decide (j = i)) as [->|?].
        * by rewrite lookup_delete Hnone.
        * rewrite lookup_delete_ne//. specialize (Hm2 j).
          revert Hm2. by rewrite lookup_insert_ne.
    - rewrite insert_delete insert_id //.
  Qed.
End big_opm.

(** todo move somewhere *)
Instance map_zip_with_ne {K} {A B C : ofeT} (f : A → B → C)
  `{Countable K} `{!EqDecision K} n :
  Proper (dist n ==> dist n ==> dist n) f →
  Proper (dist n ==> dist n ==> dist n)
    (@map_zip_with (gmap K) _ _ _ _ f).
Proof.
  intros Hf m1 m2 Hm2 m1' m2' Hm2' i.
  rewrite !map_lookup_zip_with. f_equiv =>//.
  intros x1 x2 Hx2. f_equiv =>//.
  intros y1 y2 Hy2. repeat f_equiv =>//.
Qed.
