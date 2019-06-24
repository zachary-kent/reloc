(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Notion of contextual refinement & proof that it is a precongruence wrt the logical relation *)
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From reloc.typing Require Export types interp fundamental.

From Autosubst Require Import Autosubst.

Inductive ctx_item :=
  (* λ-rec *)
  | CTX_Rec (f x: binder)
  | CTX_AppL (e2 : expr)
  | CTX_AppR (e1 : expr)
  (* Bin op *)
  | CTX_BinOpL (op : bin_op) (e2 : expr)
  | CTX_BinOpR (op : bin_op) (e1 : expr)
  (* If *)
  | CTX_IfL (e1 : expr) (e2 : expr)
  | CTX_IfM (e0 : expr) (e2 : expr)
  | CTX_IfR (e0 : expr) (e1 : expr)
  (* Products *)
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst
  | CTX_Snd
  (* Sums *)
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (e1 : expr) (e2 : expr)
  | CTX_CaseM (e0 : expr) (e2 : expr)
  | CTX_CaseR (e0 : expr) (e1 : expr)
  (* Recursive Types *)
  | CTX_Fold
  | CTX_Unfold
  (* Polymorphic Types *)
  | CTX_TLam
  | CTX_TApp
  (* Existential types *)
  (* | CTX_Pack *)
  (* | CTX_UnpackL (e' : expr) *)
  (* | CTX_UnpackR (e : expr) *)
  (* Concurrency *)
  | CTX_Fork
  (* Reference Types *)
  | CTX_Alloc
  | CTX_Load
  | CTX_StoreL (e2 : expr)
  | CTX_StoreR (e1 : expr)
  (* Compare-exchange used for fine-grained concurrency *)
  | CTX_CmpXchg_L (e1 : expr) (e2 : expr)
  | CTX_CmpXchg_M (e0 : expr) (e2 : expr)
  | CTX_CmpXchg_R (e0 : expr) (e1 : expr).

Fixpoint fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  | CTX_Rec f x => Rec f x e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  | CTX_BinOpL op e2 => BinOp op e e2
  | CTX_BinOpR op e1 => BinOp op e1 e
  | CTX_IfL e1 e2 => If e e1 e2
  | CTX_IfM e0 e2 => If e0 e e2
  | CTX_IfR e0 e1 => If e0 e1 e
  | CTX_Fold => e
  | CTX_Unfold => rec_unfold e
  | CTX_TLam => Λ: e
  | CTX_TApp => TApp e
  (* | CTX_Pack => Pack e *)
  (* | CTX_UnpackL e1 => Unpack e e1 *)
  (* | CTX_UnpackR e0 => Unpack e0 e *)
  | CTX_Fork => Fork e
  | CTX_Alloc => Alloc e
  | CTX_Load => Load e
  | CTX_StoreL e2 => Store e e2
  | CTX_StoreR e1 => Store e1 e
  | CTX_CmpXchg_L e1 e2 => CmpXchg e e1 e2
  | CTX_CmpXchg_M e0 e2 => CmpXchg e0 e e2
  | CTX_CmpXchg_R e0 e1 => CmpXchg e0 e1 e
  end.

Definition ctx := list ctx_item.

Definition fill_ctx (K : ctx) (e : expr) : expr := foldr fill_ctx_item e K.

(** typed ctx *)
Inductive typed_ctx_item :
    ctx_item → stringmap type → type → stringmap type → type → Prop :=
  | TP_CTX_Rec Γ τ τ' f x :
     typed_ctx_item (CTX_Rec f x) (<[f:=TArrow τ τ']>(<[x:=τ]>Γ)) τ' Γ (TArrow τ τ')
  | TP_CTX_AppL Γ e2 τ τ' :
     typed Γ e2 τ →
     typed_ctx_item (CTX_AppL e2) Γ (TArrow τ τ') Γ τ'
  | TP_CTX_AppR Γ e1 τ τ' :
     typed Γ e1 (TArrow τ τ') →
     typed_ctx_item (CTX_AppR e1) Γ τ Γ τ'
  | TP_CTX_PairL Γ e2 τ τ' :
     typed Γ e2 τ' →
     typed_ctx_item (CTX_PairL e2) Γ τ Γ (TProd τ τ')
  | TP_CTX_PairR Γ e1 τ τ' :
     typed Γ e1 τ →
     typed_ctx_item (CTX_PairR e1) Γ τ' Γ (TProd τ τ')
  | TP_CTX_Fst Γ τ τ' :
     typed_ctx_item CTX_Fst Γ (TProd τ τ') Γ τ
  | TP_CTX_Snd Γ τ τ' :
     typed_ctx_item CTX_Snd Γ (TProd τ τ') Γ τ'
  | TP_CTX_InjL Γ τ τ' :
     typed_ctx_item CTX_InjL Γ τ Γ (TSum τ τ')
  | TP_CTX_InjR Γ τ τ' :
     typed_ctx_item CTX_InjR Γ τ' Γ (TSum τ τ')
  | TP_CTX_CaseL Γ e1 e2 τ1 τ2 τ' :
     typed Γ e1 (TArrow τ1 τ') → typed Γ e2 (TArrow τ2 τ') →
     typed_ctx_item (CTX_CaseL e1 e2) Γ (TSum τ1 τ2) Γ τ'
  | TP_CTX_CaseM Γ e0 e2 τ1 τ2 τ' :
     typed Γ e0 (TSum τ1 τ2) → typed Γ e2 (TArrow τ2 τ') →
     typed_ctx_item (CTX_CaseM e0 e2) Γ (TArrow τ1 τ') Γ τ'
  | TP_CTX_CaseR Γ e0 e1 τ1 τ2 τ' :
     typed Γ e0 (TSum τ1 τ2) → typed Γ e1 (TArrow τ1 τ') →
     typed_ctx_item (CTX_CaseR e0 e1) Γ (TArrow τ2 τ') Γ τ'
  | TP_CTX_IfL Γ e1 e2 τ :
     typed Γ e1 τ → typed Γ e2 τ →
     typed_ctx_item (CTX_IfL e1 e2) Γ (TBool) Γ τ
  | TP_CTX_IfM Γ e0 e2 τ :
     typed Γ e0 (TBool) → typed Γ e2 τ →
     typed_ctx_item (CTX_IfM e0 e2) Γ τ Γ τ
  | TP_CTX_IfR Γ e0 e1 τ :
     typed Γ e0 (TBool) → typed Γ e1 τ →
     typed_ctx_item (CTX_IfR e0 e1) Γ τ Γ τ
  | TP_CTX_BinOpL_Nat op Γ e2 τ :
     typed Γ e2 TNat →
     binop_nat_res_type op = Some τ →
     typed_ctx_item (CTX_BinOpL op e2) Γ TNat Γ τ
  | TP_CTX_BinOpR_Nat op e1 Γ τ :
     typed Γ e1 TNat →
     binop_nat_res_type op = Some τ →
     typed_ctx_item (CTX_BinOpR op e1) Γ TNat Γ τ
  | TP_CTX_BinOpL_Bool op Γ e2 τ :
     typed Γ e2 TBool →
     binop_bool_res_type op = Some τ →
     typed_ctx_item (CTX_BinOpL op e2) Γ TBool Γ τ
  | TP_CTX_BinOpR_Bool op e1 Γ τ :
     typed Γ e1 TBool →
     binop_bool_res_type op = Some τ →
     typed_ctx_item (CTX_BinOpR op e1) Γ TBool Γ τ
  | TP_CTX_Fold Γ τ :
     typed_ctx_item CTX_Fold Γ τ.[(TRec τ)/] Γ (TRec τ)
  | TP_CTX_Unfold Γ τ :
     typed_ctx_item CTX_Unfold Γ (TRec τ) Γ τ.[(TRec τ)/]
  | TP_CTX_TLam Γ τ :
     typed_ctx_item CTX_TLam (subst (ren (+1%nat)) <$> Γ) τ Γ (TForall τ)
  | TP_CTX_TApp Γ τ τ' :
     typed_ctx_item CTX_TApp Γ (TForall τ) Γ τ.[τ'/]
  (* | TP_CTX_Pack Γ τ τ' : *)
  (*    typed_ctx_item CTX_Pack Γ τ.[τ'/] Γ (TExists τ) *)
  (* | TP_CTX_UnpackL e2 Γ τ τ2 : *)
  (*    typed (subst (ren (+1)) <$> Γ) e2 (TArrow τ (subst (ren (+1)) τ2)) → *)
  (*    typed_ctx_item (CTX_UnpackL e2) Γ (TExists τ) Γ τ2 *)
  (* | TP_CTX_UnpackR e1 Γ τ τ2 : *)
  (*    typed Γ e1 (TExists τ) → *)
  (*    typed_ctx_item (CTX_UnpackR e1) (subst (ren (+1)) <$> Γ) (TArrow τ (subst (ren (+1)) τ2))  Γ τ2 *)
  | TP_CTX_Fork Γ :
     typed_ctx_item CTX_Fork Γ TUnit Γ TUnit
  | TPCTX_Alloc Γ τ :
     typed_ctx_item CTX_Alloc Γ τ Γ (Tref τ)
  | TP_CTX_Load Γ τ :
     typed_ctx_item CTX_Load Γ (Tref τ) Γ τ
  | TP_CTX_StoreL Γ e2 τ :
     typed Γ e2 τ → typed_ctx_item (CTX_StoreL e2) Γ (Tref τ) Γ TUnit
  | TP_CTX_StoreR Γ e1 τ :
     typed Γ e1 (Tref τ) →
     typed_ctx_item (CTX_StoreR e1) Γ τ Γ TUnit
  | TP_CTX_CasL Γ e1  e2 τ :
     EqType τ → UnboxedType τ →
     typed Γ e1 τ → typed Γ e2 τ →
     typed_ctx_item (CTX_CmpXchg_L e1 e2) Γ (Tref τ) Γ (TProd τ TBool)
  | TP_CTX_CasM Γ e0 e2 τ :
     EqType τ → UnboxedType τ →
     typed Γ e0 (Tref τ) → typed Γ e2 τ →
     typed_ctx_item (CTX_CmpXchg_M e0 e2) Γ τ Γ (TProd τ TBool)
  | TP_CTX_CasR Γ e0 e1 τ :
     EqType τ → UnboxedType τ →
     typed Γ e0 (Tref τ) → typed Γ e1 τ →
     typed_ctx_item (CTX_CmpXchg_R e0 e1) Γ τ Γ (TProd τ TBool).

Inductive typed_ctx: ctx → stringmap type → type → stringmap type → type → Prop :=
  | TPCTX_nil Γ τ :
     typed_ctx nil Γ τ Γ τ
  | TPCTX_cons Γ1 τ1 Γ2 τ2 Γ3 τ3 k K :
     typed_ctx_item k Γ2 τ2 Γ3 τ3 →
     typed_ctx K Γ1 τ1 Γ2 τ2 →
     typed_ctx (k :: K) Γ1 τ1 Γ3 τ3.

(* Observable types are, at the moment, exactly the types which support equality. *)
Definition ObsType : type → Prop := EqType.

Definition ctx_refines (Γ : stringmap type)
    (e e' : expr) (τ : type) : Prop := ∀ K thp σ₀ σ₁ v τ',
  ObsType τ' →
  typed_ctx K Γ τ ∅ τ' →
  rtc erased_step ([fill_ctx K e], σ₀) (of_val v :: thp, σ₁) →
  ∃ thp' σ₁', rtc erased_step ([fill_ctx K e'], σ₀) (of_val v :: thp', σ₁').
Notation "Γ ⊨ e '≤ctx≤' e' : τ" :=
  (ctx_refines Γ e e' τ) (at level 100, e, e' at next level, τ at level 200).

Lemma typed_ctx_item_typed k Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx_item k Γ τ Γ' τ' →
  typed Γ' (fill_ctx_item k e) τ'.
Proof. induction 2; simpl; eauto using typed. Qed.

Lemma typed_ctx_typed K Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ'.
Proof. induction 2; simpl; eauto using typed_ctx_item_typed. Qed.

Instance ctx_refines_reflexive Γ τ :
  Reflexive (fun e1 e2 => ctx_refines Γ e1 e2 τ).
Proof.
  intros e K thp ? σ v τ' Hτ' Hty Hst.
  eexists _,_. apply Hst.
Qed.

Instance ctx_refines_transitive Γ τ :
  Transitive (fun e1 e2 => ctx_refines Γ e1 e2 τ).
Proof.
  intros e1 e2 e3 Hctx1 Hctx2 K thp σ₀ σ₁ v τ' Hτ' Hty Hst.
  destruct (Hctx1 K thp σ₀ σ₁ v τ' Hτ' Hty Hst) as [thp' [σ' Hst']].
  by apply (Hctx2 K thp' _ σ' v τ' Hτ').
Qed.

Lemma fill_ctx_app (K K' : ctx) (e : expr) :
  fill_ctx K' (fill_ctx K e) = fill_ctx (K' ++ K) e.
Proof. by rewrite /fill_ctx foldr_app. Qed.

Lemma typed_ctx_compose (K K' : ctx) (Γ1 Γ2 Γ3 : stringmap type) (τ1 τ2 τ3 : type) :
  typed_ctx K Γ1 τ1 Γ2 τ2 →
  typed_ctx K' Γ2 τ2 Γ3 τ3 →
  typed_ctx (K' ++ K) Γ1 τ1 Γ3 τ3.
Proof.
  revert Γ1 Γ2 Γ3 τ1 τ2 τ3.
  induction K' as [|k K'] => Γ1 Γ2 Γ3 τ1 τ2 τ3.
  - by inversion 2; simplify_eq/=.
  - intros HK.
    inversion 1 as [|? ? ? ? ? ? ? ? Hx1 Hx2]; simplify_eq/=.
    specialize (IHK' _ _ _ _ _ _ HK Hx2).
    econstructor; eauto.
Qed.

Lemma ctx_refines_congruence Γ e1 e2 τ Γ' τ' K :
  typed_ctx K Γ τ Γ' τ' →
  (Γ ⊨ e1 ≤ctx≤ e2 : τ) →
  Γ' ⊨ fill_ctx K e1 ≤ctx≤ fill_ctx K e2 : τ'.
Proof.
  intros HK Hctx K' thp σ₀ σ₁ v τ'' Hτ'' Hty.
  rewrite !fill_ctx_app => Hst.
  apply (Hctx (K' ++ K) thp σ₀ σ₁ v τ'' Hτ''); auto.
  eapply typed_ctx_compose; eauto.
Qed.

Section bin_log_related_under_typed_ctx.
  Context `{relocG Σ}.

  (* Precongruence *)
  Lemma bin_log_related_under_typed_ctx Γ e e' τ Γ' τ' K :
    (typed_ctx K Γ τ Γ' τ') →
    (□ ∀ Δ, ({Δ;Γ} ⊨ e ≤log≤ e' : τ)) -∗
      (∀ Δ, {Δ;Γ'} ⊨ fill_ctx K e ≤log≤ fill_ctx K e' : τ')%I.
  Proof.
    revert Γ τ Γ' τ' e e'.
    induction K as [|k K]=> Γ τ Γ' τ' e e'; simpl.
    - inversion_clear 1; trivial. iIntros "#H".
      iIntros (Δ). by iApply "H".
    - inversion_clear 1 as [|? ? ? ? ? ? ? ? Hx1 Hx2].
      specialize (IHK _ _ _ _ e e' Hx2).
      inversion Hx1; subst; simpl; iIntros "#Hrel";
        iIntros (Δ).
      + iApply (bin_log_related_rec with "[-]"); auto.
        iAlways. iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_app with "[]").
        iApply (IHK with "[Hrel]"); auto.
        by iApply binary_fundamental.
      + iApply (bin_log_related_app _ _ _ _ _ _ τ2 with "[]").
        by iApply binary_fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_pair with "[]").
        iApply (IHK with "[Hrel]"); auto.
        by iApply binary_fundamental.
      + iApply (bin_log_related_pair with "[]").
        by iApply binary_fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_fst.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_snd.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_injl.
        iApply (IHK with "[Hrel]"); auto.
      + iApply bin_log_related_injr.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_case with "[] []").
        iApply (IHK with "[Hrel]"); auto.
        by iApply binary_fundamental.
        by iApply binary_fundamental.
      + iApply (bin_log_related_case with "[] []").
        by iApply binary_fundamental.
        iApply (IHK with "[Hrel]"); auto.
        by iApply binary_fundamental.
      + iApply (bin_log_related_case with "[] []").
        by iApply binary_fundamental.
        by iApply binary_fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_if with "[] []");
          try by iApply binary_fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_if with "[] []");
          try by iApply binary_fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_if with "[] []");
          try by iApply binary_fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_nat_binop with "[]");
          try (by iApply binary_fundamental); eauto.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_nat_binop with "[]");
          try (by iApply binary_fundamental); eauto.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_bool_binop with "[]");
          try (by iApply binary_fundamental); eauto.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_bool_binop with "[]");
          try (by iApply binary_fundamental); eauto.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_fold with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_unfold with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_tlam with "[]").
        iIntros (τi). iAlways.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_tapp' with "[]").
        iApply (IHK with "[Hrel]"); auto.
      (* + iApply bin_log_related_pack'. *)
      (*   iApply (IHK with "[Hrel]"); auto. *)
      (* + iApply bin_log_related_unpack; try by (iIntros; fundamental). *)
      (*   iApply (IHK with "[Hrel]"); auto. *)
      (* + iApply bin_log_related_unpack; try by (iIntros; fundamental). *)
      (*   iIntros. iApply (IHK with "[Hrel]"); auto. *)
      + iApply (bin_log_related_fork with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_alloc with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_load with "[]").
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_store with "[]");
          try by iApply binary_fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_store with "[]");
          try by iApply binary_fundamental.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_CmpXchg with "[] []");
          try (by iApply binary_fundamental); eauto.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_CmpXchg with "[] []");
          try (by iApply binary_fundamental); eauto.
        iApply (IHK with "[Hrel]"); auto.
      + iApply (bin_log_related_CmpXchg with "[] []");
          try (by iApply binary_fundamental); eauto.
        iApply (IHK with "[Hrel]"); auto.
  Qed.
End bin_log_related_under_typed_ctx.
