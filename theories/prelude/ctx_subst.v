From stdpp Require Import base stringmap fin_sets fin_map_dom.
From iris.program_logic Require Export ectx_language ectxi_language.
From iris.heap_lang Require Export lang metatheory.

(** Substitution in the contexts *)
Fixpoint subst_map_ctx_item (es : stringmap val) (K : ectx_item)
         {struct K} :=
  match K with
  | AppLCtx v2 => AppLCtx v2
  | AppRCtx e1 => AppRCtx (subst_map es e1)
  | UnOpCtx op => UnOpCtx op
  | BinOpLCtx op v2 => BinOpLCtx op v2
  | BinOpRCtx op e1 => BinOpRCtx op (subst_map es e1)
  | IfCtx e1 e2 => IfCtx (subst_map es e1) (subst_map es e2)
  | PairLCtx v2 => PairLCtx v2
  | PairRCtx e1 => PairRCtx (subst_map es e1)
  | FstCtx => FstCtx
  | SndCtx => SndCtx
  | InjLCtx => InjLCtx
  | InjRCtx => InjRCtx
  | CaseCtx e1 e2 => CaseCtx (subst_map es e1) (subst_map es e2)
  | AllocNLCtx v2 => AllocNLCtx v2
  | AllocNRCtx e1 => AllocNRCtx (subst_map es e1)
  | FreeCtx => FreeCtx
  | LoadCtx => LoadCtx
  | StoreLCtx v2 => StoreLCtx v2
  | StoreRCtx e1 => StoreRCtx (subst_map es e1)
  | XchgLCtx v2 => XchgLCtx v2
  | XchgRCtx e1 => XchgRCtx (subst_map es e1)
  | CmpXchgLCtx v1 v2 => CmpXchgLCtx v1 v2
  | CmpXchgMCtx e0 v2 => CmpXchgMCtx (subst_map es e0) v2
  | CmpXchgRCtx e0 e1 => CmpXchgRCtx (subst_map es e0) (subst_map es e1)
  | FaaLCtx v2 => FaaLCtx v2
  | FaaRCtx e1 => FaaRCtx (subst_map es e1)
  | ResolveLCtx Ki v1 v2 => ResolveLCtx (subst_map_ctx_item es Ki) v1 v2
  | ResolveMCtx e0 v2 => ResolveMCtx (subst_map es e0) v2
  | ResolveRCtx e0 e1 => ResolveRCtx (subst_map es e0) (subst_map es e1)
  end.

Definition subst_map_ctx (es : stringmap val) (K : list ectx_item) :=
  map (subst_map_ctx_item es) K.

Lemma subst_map_fill_item (vs : stringmap val) (Ki : ectx_item) (e : expr)  :
  subst_map vs (fill_item Ki e) =
  fill_item (subst_map_ctx_item vs Ki) (subst_map vs e).
Proof. induction Ki; simpl; eauto with f_equal. Qed.

Lemma subst_map_fill (vs : stringmap val) (K : list ectx_item) (e : expr) :
  subst_map vs (fill K e) = fill (subst_map_ctx vs K) (subst_map vs e).
Proof.
  generalize dependent e. generalize dependent vs.
  induction K as [|Ki K]; eauto.
  intros es e. simpl.
  by rewrite IHK subst_map_fill_item.
Qed.
