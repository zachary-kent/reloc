(* ReLoC -- Relational logic for fine-grained concurrency *)
(** An alternative to `PureExec` *)
From iris.heap_lang Require Export lang notation proofmode metatheory.

Class PureClosed ϕ n (e1 e2 : expr) :=
  pureexec_subst_map : ∀ vs, PureExec ϕ n (subst_map vs e1) (subst_map vs e2).

Ltac solve_pure_exec := intros vs; simpl; apply _.

Instance pure_pairc (v1 v2 : val) :
  PureClosed True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
Instance pure_injlc (v : val) :
  PureClosed True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
Instance pure_injrc (v : val) :
  PureClosed True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

(** TODO : Move to metatheory *)
Lemma subst_map_subst vs x v e :
  subst_map vs (subst x v e) =
  subst_map (<[x:=v]> vs) e.
Proof.
  revert vs.
  assert (∀ x f vs, BNamed x ≠ f → binder_delete f (<[x:=v]> vs) = <[x:=v]>(binder_delete f vs)) as Hdel.
  { intros ? [|?] vs =>/= // He. rewrite delete_insert_ne // =>?. apply He; by subst. }
  induction e=> vs; simplify_map_eq; auto with f_equal.
  - match goal with
    | |- context [ <[?x:=_]> _ !! ?y ] =>
       destruct (decide (x = y)); simplify_map_eq=> //
    end.
  - f_equal. destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + etrans. apply IHe. rewrite !Hdel //.
    + simpl. by rewrite delete_insert_delete.
    + rewrite Hdel // /=. by rewrite delete_insert_delete.
Qed.
Lemma subst_map_subst' vs x v e :
  subst_map vs (subst' x v e) =
  subst_map (binder_insert x v vs) e.
Proof. destruct x; eauto using subst_map_subst. Qed.

Instance pure_unop op v v' :
  PureClosed (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

Instance pure_binop op v1 v2 v' :
  PureClosed (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v').
Proof. solve_pure_exec. Qed.

Instance pure_if_true e1 e2 : PureClosed True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Instance pure_if_false e1 e2 : PureClosed True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Instance pure_fst v1 v2 :
  PureClosed True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

Instance pure_snd v1 v2 :
  PureClosed True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

Instance pure_case_inl v e1 e2 :
  PureClosed True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

Instance pure_case_inr v e1 e2 :
  PureClosed True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

(** Closedness condition are required for lambdas *)
Class ClosedExpr (e : expr) := closed_expr : is_closed_expr [] e.
Hint Extern 0 (ClosedExpr _) => compute; reflexivity : typeclass_instances.

Instance pure_beta f x (erec : expr) (v1 v2 : val) `{AsRecV v1 f x erec} :
  ClosedExpr (Rec f x erec) →
  PureClosed True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof.
  rewrite (@as_recv v1). simpl.
  intros Hcl vs. simpl.
  rewrite subst_map_subst'.
  rewrite subst_map_binder_insert.
  rewrite subst_map_subst'.
  rewrite subst_map_binder_insert.
  enough ((subst_map (binder_delete f (binder_delete x vs)) erec) = erec) as ->;
    first apply _.
  eapply subst_map_is_closed=> // y.
  admit.
Admitted.

Instance pure_recc f x (erec : expr) :
  ClosedExpr (Rec f x erec) →
  PureClosed True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof.
  move=>/= Herec vs /=.
  enough ((subst_map (binder_delete x (binder_delete f vs)) erec) = erec) as ->;
    first apply _.
  admit.
Admitted.

(* TODO: this is needed to reduce (v ;; t) → t for an arbitrary expression t. *)
Instance pure_seq v (t : expr) :
  PureClosed True 2 (Val v;; t) t.
Proof.
  intros vs. simpl.
  assert (AsRecV (λ: <>, (subst_map vs t)) <> <> (subst_map vs t)).
  { by unlock. }
  intros _. eapply (nsteps_trans 1 1); last first.
  { set (L := lifting.pure_beta BAnon BAnon (subst_map vs t) _ v).
    rewrite <- lock in L. simpl in *. by apply L. }
  eapply (pure_exec_fill [AppLCtx v]); [apply _|done].
Qed.
