(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Polymorphic equality check macro. *)
From reloc Require Import reloc typing.fundamental.

Fixpoint polyeq (τ : type) : val :=
  match τ with
  | TUnit => λ: "x" "y", #true
  | TNat => λ: "x" "y", "x" = "y"
  | TBool => λ: "x" "y", "x" = "y"
  | TSum τ1 τ2 => λ: "x" "y",
                  match: "x" with
                    InjL "x" =>
                    match: "y" with
                      InjL "y" => (polyeq τ1) "x" "y"
                    | InjR <> => #false
                    end
                  | InjR "x" =>
                    match: "y" with
                      InjL <> => #false
                    | InjR "y" => (polyeq τ2) "x" "y"
                    end
                  end
  | TProd τ1 τ2 => λ: "x" "y", polyeq τ1 (Fst "x") (Fst "y") &&
                               polyeq τ2 (Snd "x") (Snd "y")
  | TRef _ => λ: "x" "y", "x" = "y"
  | _ => λ: "x" "y", #false
  end.

Section proof.
  Context `{!relocG Σ}.

  Lemma polyeq_true τ v1 v2 :
    EqType τ →
    interp τ [] v1 v2 ⊢
    REL polyeq τ v1 v2 << #true : lrel_bool.
  Proof.
    intros Hτ ; revert v1 v2. induction Hτ=> v1 v2 /=.
    - iDestruct 1 as "[-> ->]". rel_pures_l. rel_values.
    - iDestruct 1 as (z) "[-> ->]". rel_pures_l.
      rewrite bool_decide_true//. rel_values.
    - iDestruct 1 as (z) "[-> ->]". rel_pures_l.
      rewrite bool_decide_true//. rel_values.
    - iDestruct 1 as (w1 w2 u1 u2 -> ->) "[Hw Hu]". rel_pures_l.
      rewrite IHHτ1 IHHτ2.
      rel_bind_r _.
      rel_bind_l (polyeq τ _ _). iApply (refines_bind with "Hw").
      iIntros (v v'). iDestruct 1 as (b) "[-> ->]". simpl.
      destruct b; rel_pures_l; eauto. rel_values.
    - iDestruct 1 as (w1 w2) "[(->&->&H)|(->&->&H)]"; rel_pures_l.
      + by iApply IHHτ1.
      + by iApply IHHτ2.
  Qed.

End proof.
