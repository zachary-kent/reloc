From stdpp Require Export tactics.
From iris.algebra Require Export ofe.

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
