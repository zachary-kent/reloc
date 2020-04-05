From reloc.typing Require Export types contextual_refinement.

Lemma tac_ctx_bind_l e' C Γ e t τ :
  e = fill_ctx C e' →
  ctx_refines Γ (fill_ctx C e') t τ →
  ctx_refines Γ e t τ.
Proof. intros; subst; assumption. Qed.

Lemma tac_ctx_bind_r e' C Γ e t τ :
  e = fill_ctx C e' →
  ctx_refines Γ t (fill_ctx C e') τ →
  ctx_refines Γ t e τ.
Proof. intros; subst; assumption. Qed.

Ltac reshape_expr_ctx e tac :=
  let rec go K e :=
    match e with
    | _                     => tac (reverse K) e
    (* Base lambda calculus *)

    | Rec ?f ?x ?e          => add_item (CTX_Rec f x) K e
    | App ?e1 ?e2           => add_item (CTX_AppL e2) K e1
    | App ?e1 ?e2           => add_item (CTX_AppR e1) K e2
    (* Base types and their operations *)
    | UnOp ?op ?e           => add_item (UnOpCtx op) K e
    | BinOp ?op ?e1 ?e2     => add_item (CTX_BinOpL op e2) K e1
    | BinOp ?op ?e1 ?e2     => add_item (CTX_BinOpR op e1) K e2
    | If ?e0 ?e1 ?e2        => add_item (CTX_IfL e1 e2) K e0
    | If ?e0 ?e1 ?e2        => add_item (CTX_IfM e0 e2) K e1
    | If ?e0 ?e1 ?e2        => add_item (CTX_IfR e0 e1) K e2
    (* Products *)
    | Pair ?e1 ?e2          => add_item (CTX_PairL e2) K e1
    | Pair ?e1 ?e2          => add_item (CTX_PairR e1) K e2
    | Fst ?e                => add_item CTX_Fst K e
    | Snd ?e                => add_item CTX_Snd K e
    (* Sums *)
    | InjL ?e               => add_item CTX_InjL K e
    | InjR ?e               => add_item CTX_InjR K e
    | Case ?e0 ?e1 ?e2      => add_item (CTX_CaseL e1 e2) K e0
    | Case ?e0 ?e1 ?e2      => add_item (CTX_CaseM e0 e2) K e1
    | Case ?e0 ?e1 ?e2      => add_item (CTX_CaseR e0 e1) K e2
    (* Concurrency *)
    | Fork ?e               => add_item CTX_Fork K e
    (* Heap *)
    | Alloc  ?e             => add_item CTX_Alloc K e
    | Load ?e               => add_item CTX_Load K e
    | Store ?e1 ?e2         => add_item (CTX_StoreR e1) K e2
    | Store ?e1 ?e2         => add_item (CTX_StoreL e2) K e1
    (* Compare-exchange *)
    | CmpXchg ?e0 ?e1 ?e2   => add_item (CTX_CmpXchgL e1 e2) K e0
    | CmpXchg ?e0 ?e1 ?e2   => add_item (CTX_CmpXchgM e0 e2) K e1
    | CmpXchg ?e0 ?e1 ?e2   => add_item (CTX_CmpXchgR e0 e1) K e2
    | FAA ?e0 ?e1           => add_item (CTX_FAAL e1) K e0
    | FAA ?e0 ?e1           => add_item (CTX_FAAR e0) K e1
    end
  with add_item Ki K e := go (Ki :: K) e
  in
  go (@nil ctx_item) e.

Ltac ctx_bind_helper :=
  simpl;
  lazymatch goal with
  | |- fill_ctx ?K ?e = fill_ctx _ ?efoc =>
     reshape_expr_ctx e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill_ctx K e) with (fill_ctx K'' e') by (by rewrite ?fill_ctx_app))
  | |- ?e = fill_ctx _ ?efoc =>
     reshape_expr_ctx e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill_ctx K' e') by (by rewrite ?fill_ctx_app))
  end; reflexivity.

Tactic Notation "ctx_bind_l" open_constr(efoc) :=
  eapply (tac_ctx_bind_l efoc);
  [ ctx_bind_helper
  | (* new goal *)
  ].

Tactic Notation "ctx_bind_r" open_constr(efoc) :=
  eapply (tac_ctx_bind_r efoc);
  [ ctx_bind_helper
  | (* new goal *)
  ].
