(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Interpretations for System F_mu_ref types *)
From iris.algebra Require Import list.
From reloc.typing Require Export types.
From reloc.logic Require Import model.
From Autosubst Require Import Autosubst.

Section semtypes.
  Context `{relocG Σ}.

  (** Type-level lambdas are interpreted as closures *)

  Definition lty2_forall (C : lty2 → lty2) : lty2 := Lty2 (λ w1 w2,
    □ ∀ A : lty2, interp_expr ⊤ (TApp w1) (TApp w2) (C A))%I.

  Definition lty2_exists (C : lty2 → lty2) : lty2 := Lty2 (λ w1 w2,
    ∃ A : lty2, C A w1 w2)%I.

  Definition lty2_true : lty2 := Lty2 (λ w1 w2, True)%I.

  Program Definition ctx_lookup (x : var) : listC lty2C -n> lty2C := λne Δ,
    (from_option id lty2_true (Δ !! x))%I.
  Next Obligation.
    intros x n Δ Δ' HΔ.
    destruct (Δ !! x) as [P|] eqn:HP; cbn in *.
    - eapply (Forall2_lookup_l _ _ _ x P) in HΔ; last done.
      destruct HΔ as (Q & HQ & HΔ).
      rewrite HQ /= //.
    - destruct (Δ' !! x) as [Q|] eqn:HQ; last reflexivity.
      eapply (Forall2_lookup_r _ _ _ x Q) in HΔ; last done.
      destruct HΔ as (P & HP' & HΔ). exfalso.
      rewrite HP in HP'. inversion HP'.
  Qed.

  Instance lty2_prod_ne n : Proper (dist n ==> (dist n ==> dist n)) lty2_prod.
  Proof.
    intros A A' HA B B' HB.
    intros w1 w2. cbn.
    unfold lty2_prod, lty2_car. cbn.
    (* TODO: why do we have to unfold lty2_car here? *)
    repeat f_equiv; eauto.
  Qed.

  Instance lty2_sum_ne n : Proper (dist n ==> (dist n ==> dist n)) lty2_sum.
  Proof.
    intros A A' HA B B' HB.
    intros w1 w2. cbn.
    unfold lty2_sum, lty2_car. cbn.
    (* TODO: why do we have to unfold lty2_car here? *)
    repeat f_equiv; eauto.
  Qed.

  Instance lty2_arr_ne n : Proper (dist n ==> (dist n ==> dist n)) lty2_arr.
  Proof.
    intros A A' HA B B' HB.
    intros w1 w2. cbn.
    unfold lty2_sum, lty2_car. cbn.
    (* TODO: why do we have to unfold lty2_car here? *)
    repeat f_equiv; eauto.
  Qed.

  Instance lty2_rec_ne n : Proper (dist n ==> dist n)
                                   (lty2_rec : (lty2C -n> lty2C) -> lty2C).
  Proof.
    intros F F' HF.
    unfold lty2_rec, lty2_car.
    apply fixpoint_ne=> X w1 w2.
    unfold lty2_rec1, lty2_car. cbn.
    f_equiv.
    apply lty2_car_ne; eauto.
  Qed.

  Program Fixpoint interp (τ : type) : listC lty2C -n> lty2C :=
    match τ as _ return _ with
    | TUnit => λne _, lty2_unit
    | TNat => λne _, lty2_int
    | TBool => λne _, lty2_bool
    | TProd τ1 τ2 => λne Δ, lty2_prod (interp τ1 Δ) (interp τ2 Δ)
    | TSum τ1 τ2 => λne Δ, lty2_sum (interp τ1 Δ) (interp τ2 Δ)
    | TArrow τ1 τ2 => λne Δ, lty2_arr (interp τ1 Δ) (interp τ2 Δ)
    | TRec τ' => λne Δ, lty2_rec (λne τ, interp τ' (τ::Δ))
    | TVar x => ctx_lookup x
    | TForall τ' => λne Δ, lty2_forall (λ τ, interp τ' (τ::Δ))
    | TExists τ' => λne Δ, lty2_exists (λ τ, interp τ' (τ::Δ))
    | Tref τ => λne Δ, lty2_ref (interp τ Δ)
    end.
  Solve Obligations with (intros I τ τ' n Δ Δ' HΔ' ??; solve_proper).
  Next Obligation.
    intros I τ τ' n Δ Δ' HΔ' ??.
    apply lty2_rec_ne=> X /=.
    apply I. by f_equiv.
  Defined.

End semtypes.
