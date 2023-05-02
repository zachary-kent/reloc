(** Some arithmetical facts that we use in the MPMC queue case study *)
From Coq Require Import ssreflect.
From stdpp Require Import prelude base.

(* TODO: move to std++? *)
Lemma false_Is_true: ∀ b : bool, ¬ b →  b = false.
Proof.
  intros b Hb.
  by apply negb_true_iff, Is_true_eq_true, negb_prop_intro.
Qed.

(* Even/odd *)
Lemma Even_mul2 k : Nat.Even (2 * k).
Proof.
  assert (2 * k = 0 + 2 * k) as -> by lia.
  apply Nat.even_spec.
  by rewrite Nat.even_add_mul_2.
Qed.
Lemma Odd_mul2 k : ¬ Nat.Odd (2 * k).
Proof.
  assert (2 * k = 0 + 2 * k) as -> by lia.
  rewrite -Nat.odd_spec.
  by rewrite Nat.odd_add_mul_2.
Qed.
Lemma Odd_succ k : Nat.Odd (2 * k + 1).
Proof.
  assert (2 * k + 1 = 1 + 2 * k) as -> by lia.
  apply Nat.odd_spec.
  by rewrite Nat.odd_add_mul_2.
Qed.
Lemma even_succ k : ¬ Nat.even (S (2 * k)).
Proof.
  assert (S (2 * k) = 1 + 2 * k) as -> by lia.
  apply negb_prop_elim.
  by rewrite Nat.even_add_mul_2.
Qed.
Lemma even_lift k : Nat.Even k ↔ Nat.even k.
Proof.
  split; intro.
  - by apply Is_true_eq_left, Nat.even_spec.
  - by apply Nat.even_spec, Is_true_eq_true.
Qed.
Lemma odd_lift k : Nat.Odd k ↔ Nat.odd k.
Proof.
  split; intro.
  - by apply Is_true_eq_left, Nat.odd_spec.
  - by apply Nat.odd_spec, Is_true_eq_true.
Qed.
Lemma Even_succ k : ¬ Nat.Even (S (2 * k)).
Proof. rewrite even_lift. apply even_succ. Qed.

Lemma even_odd_case x :
  (Nat.even x = true /\ exists z, x = 2 * z) \/
  (Nat.even x = false /\ exists z, x = S (2 * z)).
Proof.
  induction x as [|x].
  - left. split; eauto.
  - destruct IHx as [[IHx [z ->]]|[IHx [z ->]]]; [right|left].
    + split; last eauto.
      apply false_Is_true.
      rewrite -even_lift.
      apply Even_succ.
    + split.
      * assert (S (S (2 * z)) = 2 * (S z)) as -> by lia.
        apply Is_true_eq_true.
        rewrite -even_lift.
        apply Even_mul2.
      * exists (S z). lia.
Qed.

Lemma even_odd_spec n :
  (Nat.even n = true ∧ Nat.odd n = false) ∨ (Nat.even n = false ∧ Nat.odd n = true).
Proof.
  destruct (Nat.Even_or_Odd n) as [H%Nat.even_spec|H%Nat.odd_spec].
  - left. split; first done. by rewrite -Nat.negb_even H.
  - right. split; last done. by rewrite -Nat.negb_odd H.
Qed.

Lemma ltb_lt_1 n m : n < m → (n <? m) = true.
Proof. apply Nat.ltb_lt. Qed.

(* This is just [Nat.mul_comm] with things ordered differently. *)
Lemma div_mod' (x y : nat) : y ≠ 0 →  (x `div` y) * y + x `mod` y = x.
Proof. symmetry. rewrite Nat.mul_comm. apply Nat.div_mod. done. Qed.

(* why is there an extra condition in Nat.mod_0_l? *)
Lemma mod0 (a : nat) : 0 `mod` a = 0.
Proof.
  destruct a; first done.
  by apply Nat.Div0.mod_0_l.
Qed.
Lemma div0 (a : nat) : 0 `div` a = 0.
Proof.
  destruct a; first done.
  by apply Nat.Div0.div_0_l.
Qed.


Lemma set_seq_take_start `{SemiSet nat C} (start len1 len2 : nat) :
  len2 <= len1 →
  set_seq (C:=C) start len1 ≡ (set_seq start len2) ∪ (set_seq (start + len2) (len1 - len2)).
Proof. intros Hle. set_solver by lia. Qed.

Lemma set_seq_take_start_L `{SemiSet nat C, !LeibnizEquiv C} (start len1 len2 : nat) :
  len2 <= len1 →
  set_seq (C:=C) start len1 = (set_seq start len2) ∪ (set_seq (start + len2) (len1 - len2)).
Proof. set_solver by lia. Qed.

Lemma drop_nth {B : Type} i m (x : B) xs : drop i m = x :: xs → m !! i = Some x.
Proof.
  generalize dependent m.
  induction i as [|? IH]; intros m.
  - rewrite drop_0. intros ->. done.
  - destruct m; first done. rewrite skipn_cons. apply IH.
Qed.

Lemma drop_ge_2 {B : Type} (l : list B) n : drop n l = [] → length l ≤ n.
Proof.
  generalize dependent l.
  induction n as [|? IH]; intros l.
  - destruct l; done.
  - destruct l; simpl; first lia. intros H%IH. lia.
Qed.
