From stdpp Require Import base decidable.
From iris.algebra Require Import numbers cmra excl.
From reloc.prelude Require Import arith.

(* A camera of, potentially, infinite sets. Most of the lemmas are about sets of
   natural numbers. *)

Definition setUR (A : Type) := discrete_funUR (λ (a : A), optionUR (exclR unitO)).

(* Sets of natural numbers. *)

(* Create a set from a characteristic function. *)
Definition set_cf {A : Type} (f : A → bool) : setUR A :=
  λ a, if f a then Some (Excl ()) else None.

Definition set_of (A : Type) := @set_cf A (const true).

Definition set_singleton `{!EqDecision A} (a : A) :=
  set_cf (λ a', if decide (a = a') then true else false).

Definition set_nat := set_of nat.
Definition set_even := set_cf even.
Definition set_odd := set_cf odd.

Lemma split_even_odd : set_nat ≡ set_even ⋅ set_odd.
Proof.
  intros n. rewrite /set_even /set_odd /set_cf. simpl.
  rewrite discrete_fun_lookup_op.
  destruct (even_odd_spec n) as [[-> ->]|[-> ->]]; done.
Qed.

(* Set of nats including and above n. *)
Definition set_above n := set_cf (λ n', n <=? n').

Definition set_upto n := set_cf (λ n', n' <? n).

Lemma set_above_lookup n m : n ≤ m → set_above n m = Excl' ().
Proof. rewrite /set_above /set_cf. by intros ->%leb_le. Qed.

Lemma set_above_lookup_none n m : m < n → (set_above n) m = None.
Proof. rewrite /set_above /set_cf. by intros ->%Nat.leb_gt. Qed.

Lemma set_upto_lookup n m : m < n → (set_upto n) m = Excl' ().
Proof. rewrite /set_upto /set_cf. by intros ->%Nat.ltb_lt. Qed.

Lemma set_upto_lookup_none n m : n ≤ m → (set_upto n) m = None.
Proof. rewrite /set_upto /set_cf. by intros ->%Nat.ltb_ge. Qed.

Lemma set_above_zero : set_above 0 ≡ set_nat.
Proof. intros n. rewrite set_above_lookup; [done | lia]. Qed.

Lemma set_upto_zero : set_upto 0 ≡ ε.
Proof.
  intros n. rewrite /set_upto /set_cf.
  assert (n <? 0 = false) as ->; last done.
  apply leb_correct_conv. lia.
Qed.

Lemma discrete_fun_valid' (s : setUR nat) (n : nat) : ✓ s → ✓ (s n).
Proof. done. Qed.

Lemma set_singleton_lookup (n : nat) : set_singleton n n = Excl' ().
Proof. rewrite /set_singleton /set_cf. rewrite decide_True; done. Qed.

Lemma set_singleton_lookup_none (n m : nat) : n ≠ m → set_singleton n m = None.
Proof.
  intros H. rewrite /set_singleton /set_cf. rewrite decide_False; done.
Qed.

Lemma set_singleton_invalid (n : nat) : ¬ ✓ (set_singleton n ⋅ set_singleton n).
Proof.
  rewrite /set_singleton /set_cf.
  intros Hv.
  pose proof (Hv n) as Hv.
  rewrite discrete_fun_lookup_op in Hv.
  rewrite decide_True in Hv; done.
Qed.

Lemma set_singletons_valid (n m : nat) : ✓ (set_singleton n ⋅ set_singleton m) → n ≠ m.
Proof.
  intros Hv ->.
  by apply set_singleton_invalid in Hv.
Qed.

(* Rewrite n <? m when true *)
Hint Rewrite ltb_lt_1 using lia : natb.
Hint Rewrite leb_correct_conv using lia : natb.
Hint Rewrite leb_correct using lia : natb.
Hint Rewrite set_above_lookup using lia : natb.
Hint Rewrite @decide_False using lia : natb.
Hint Rewrite @decide_True using lia : natb.
Hint Rewrite set_above_lookup_none using lia : natb.
Hint Rewrite set_upto_lookup_none using lia : natb.
Hint Rewrite set_upto_lookup using lia : natb.
Hint Rewrite set_singleton_lookup_none using lia : natb.
Hint Rewrite set_singleton_lookup using lia : natb.
Hint Rewrite div_mod' : natb.
Hint Rewrite mod0 : natb.
Hint Rewrite div0 : natb.
Hint Rewrite Nat.add_0_r : natb.
Hint Rewrite Nat.add_0_l : natb.
Hint Rewrite Nat.ltb_irrefl : natb.
Hint Rewrite Nat.max_0_r : natb.
Hint Rewrite Nat.max_0_l : natb.

Lemma set_upto_singleton_valid n m : ✓ (set_upto n ⋅ set_singleton m) → n ≤ m.
Proof.
  destruct (le_gt_dec n m); first done.
  intros Hv.
  pose proof (Hv m).
  rewrite discrete_fun_lookup_op in H.
  rewrite /set_singleton /set_cf in H.
  autorewrite with natb in H.
  done.
Qed.

Lemma take_first n : set_above n ≡ set_singleton n ⋅ set_above (n + 1).
Proof.
  intros n'.
  rewrite /set_singleton. rewrite /set_cf.
  rewrite discrete_fun_lookup_op.
  destruct (le_lt_dec n n').
  - autorewrite with natb.
    destruct (le_lt_or_eq n n' l); autorewrite with natb; done.
  - autorewrite with natb. done.
Qed.

Lemma set_upto_singleton n : set_singleton n ⋅ set_upto n ≡ set_upto (n + 1).
Proof.
  intros m.
  rewrite discrete_fun_lookup_op.
  destruct (le_gt_dec m n).
  - rewrite (set_upto_lookup (n + 1)); last lia.
    destruct (le_lt_or_eq m n l).
    * autorewrite with natb. done.
    * subst. autorewrite with natb. done.
  - autorewrite with natb. done.
Qed.

(* Create a set from a decidable predicate. *)
Definition set_prop {A : Type} (f : A → Prop) `{!∀ a, Decision (f a)} : setUR A :=
  λ a, if decide (f a) then Some (Excl ()) else None.

(* All even numbers except for the first n. *)
Definition set_even_drop n := set_cf (λ n', (even n') && (2 * n <=? n')).

(* All odd numbers except for the first n. *)
Definition set_odd_drop n := set_cf (λ n', (odd n') && (2 * n + 1 <=? n')).

Lemma set_even_drop_lookup n m : Even m → 2 * n ≤ m → set_even_drop n m = Excl' ().
Proof.
  intros He Hle.
  rewrite /set_even_drop /set_cf.
  assert (Nat.even m = true) as -> by by apply Nat.even_spec.
  rewrite leb_correct; last done.
  done.
Qed.

Lemma set_even_drop_zero : set_even_drop 0 ≡ set_even.
Proof.
  intros n.
  rewrite /set_even_drop /set_even /set_cf.
  destruct (Nat.even n); done.
Qed.

Lemma set_odd_drop_zero : set_odd_drop 0 ≡ set_odd.
Proof.
  intros n.
  rewrite /set_odd_drop /set_odd /set_cf.
  destruct n; first done.
  destruct (Nat.odd (S n)); done.
Qed.

Lemma set_even_drop_singleton n : set_even_drop n ≡ set_even_drop (n + 1) ⋅ set_singleton (2 * n).
Proof.
  intros m.
  rewrite /set_even_drop /set_singleton /set_cf /=.
  autorewrite with natb.
  rewrite discrete_fun_lookup_op.
  destruct (Nat.Even_or_Odd m) as [[a b]|[a b]].
  - replace (Nat.even m) with true.
    + destruct (gt_eq_gt_dec m (n + n)) as [[He|He]|He]; autorewrite with natb; eauto.
    + symmetry. apply Nat.even_spec. by econstructor.
  - replace (Nat.even m) with false.
    + by autorewrite with natb.
    + rewrite -Nat.negb_odd.
      cut (Nat.odd m = true); first by intros ->.
      eapply Nat.odd_spec. by econstructor.
Qed.

Lemma set_odd_drop_singleton n : set_odd_drop n ≡ set_odd_drop (n + 1) ⋅ set_singleton (2 * n + 1).
Proof.
  intros m.
  rewrite /set_odd_drop /set_singleton /set_cf /=.
  autorewrite with natb.
  rewrite discrete_fun_lookup_op.
  destruct (Nat.Even_or_Odd m) as [[a b]|[a b]].
  - replace (Nat.odd m) with false.
    + destruct (gt_eq_gt_dec m (n + n)) as [[He|He]|He]; autorewrite with natb; eauto.
    + rewrite -Nat.negb_even.
      cut (Nat.even m = true); first by intros ->.
      eapply Nat.even_spec. by econstructor.
  - replace (Nat.odd m) with true.
    + destruct (gt_eq_gt_dec m (n + n)) as [[He|He]|He];
        autorewrite with natb; try lia; eauto.
      destruct (gt_eq_gt_dec m ((n+1) + (n+1))) as [[He1|He1]|He1];
        autorewrite with natb; try lia; eauto.
    + symmetry. apply Nat.odd_spec. by econstructor.
Qed.
