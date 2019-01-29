(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Interpretations for System F_mu_ref types *)
From iris.algebra Require Export list.
From reloc.typing Require Export types.
From reloc.logic Require Import model.
From Autosubst Require Import Autosubst.

Section semtypes.
  Context `{relocG Σ}.

  (** Type-level lambdas are interpreted as closures *)

  (** DF: lty2_forall is defined here because it depends on TApp *)
  Definition lty2_forall (C : lty2 → lty2) : lty2 := Lty2 (λ w1 w2,
    □ ∀ A : lty2, interp_expr ⊤ (TApp w1) (TApp w2) (C A))%I.

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

  Program Fixpoint interp (τ : type) : listC lty2C -n> lty2C :=
    match τ as _ return listC lty2C -n> lty2C with
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

  Definition bin_log_related (E : coPset)
             (Δ : list lty2) (Γ : stringmap type)
             (e e' : expr) (τ : type) : iProp Σ :=
    {E;fmap (λ τ, interp τ Δ) Γ} ⊨ e << e' : (interp τ Δ).

End semtypes.

Notation "'{' E ';' Δ ';' Γ '}' ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related E Δ Γ e%E e'%E (τ)%F)
  (at level 100, E at next level, Δ at next level, Γ at next level, e, e' at next level,
   τ at level 200,
   format "'[hv' '{' E ';'  Δ ';'  Γ '}'  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  :  τ ']'").
Notation "'{' Δ ';' Γ '}' ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related ⊤ Δ Γ e%E e'%E (τ)%F)
  (at level 100, Δ at next level, Γ at next level, e, e' at next level,
   τ at level 200,
   format "'[hv' '{' Δ ';'  Γ '}'  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  :  τ ']'").

Section props.
  Context `{relocG Σ}.

  Lemma fupd_logrel E1 E2 Δ Γ e e' τ :
    ((|={E1,E2}=> {E2;Δ;Γ} ⊨ e ≤log≤ e' : τ)
     -∗ {E1;Δ;Γ} ⊨ e ≤log≤ e' : τ)%I.
  Proof. apply fupd_logrel. Qed.

End props.

Notation "⤉ Γ" := (Autosubst_Classes.subst (ren (+1)%nat) <$> Γ) (at level 10, format "⤉ Γ").
