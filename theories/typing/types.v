(* ReLoC -- Relational logic for fine-grained concurrency *)
(** (Syntactic) Typing for System F_mu_ref with existential types and concurrency *)
From Autosubst Require Export Autosubst.
From stdpp Require Export stringmap.
From iris.heap_lang Require Export lang notation metatheory.

(** * Types *)
Inductive type :=
  | TUnit : type
  | TNat : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TForall (τ : {bind 1 of type})
  | TExists (τ : {bind 1 of type})
  | Tref (τ : type).

(** Which types support equality testing *)
Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TNat
  | EqTBool : EqType TBool
  | EqTProd τ τ' : EqType τ → EqType τ' → EqType (TProd τ τ')
  | EqSum τ τ' : EqType τ → EqType τ' → EqType (TSum τ τ').

(** Which types are unboxed *)
Inductive UnboxedType : type → Prop :=
  | UnboxedTUnit : UnboxedType TUnit
  | UnboxedTNat : UnboxedType TNat
  | UnboxedTBool : UnboxedType TBool
  | UnboxedTref τ : UnboxedType (Tref τ).

(** Autosubst instances *)
Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Fixpoint binop_nat_res_type (op : bin_op) : option type :=
  match op with
  | MultOp => Some TNat | PlusOp => Some TNat | MinusOp => Some TNat
  | EqOp => Some TBool | LeOp => Some TBool | LtOp => Some TBool
  | _ => None
  end.
Fixpoint binop_bool_res_type (op : bin_op) : option type :=
  match op with
  | XorOp => Some TBool | EqOp => Some TBool
  | _ => None
  end.

Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Infix "*" := TProd : FType_scope.
Notation "(*)" := TProd (only parsing) : FType_scope.
Infix "+" := TSum : FType_scope.
Notation "(+)" := TSum (only parsing) : FType_scope.
Infix "→" := TArrow : FType_scope.
Notation "(→)" := TArrow (only parsing) : FType_scope.
Notation "μ: τ" :=
  (TRec τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∀: τ" :=
  (TForall τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∃: τ" :=
  (TExists τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "'ref' τ" := (Tref τ%ty) (at level 10, τ at next level, right associativity): FType_scope.

(** * Typing judgements *)
Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
Reserved Notation "⊢ᵥ v : τ" (at level 20, v, τ at next level).

(* Shift all the indices in the context by one,
   used when inserting a new type interpretation in Δ. *)
Notation "⤉ Γ" := (Autosubst_Classes.subst (ren (+1)%nat) <$> Γ) (at level 10, format "⤉ Γ").

(** We model type-level lambdas and applications as thunks *)
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing).
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.
Notation "'TApp' e" := (App e%E #()%E) (at level 200, only parsing).

(* To unfold a recursive type, we need to take a step. We thus define the
unfold operator to be the identity function. *)
Definition rec_unfold : val := λ: "x", "x".
Definition unpack : val := λ: "x" "y", "y" "x".

Notation "'unpack:' x := e1 'in' e2" := (unpack e1%E (Lam x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200, only parsing,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : expr_scope.

Notation "'unpack:' x := e1 'in' e2" := (unpack e1%E (LamV x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200, only parsing,
   format "'[' 'unpack:'  x  :=  '[' e1 ']'  'in'  '/' e2 ']'") : val_scope.

(** Operation lifts *)
Instance insert_binder (A : Type): Insert binder A (stringmap A) :=
  binder_insert.

(** Typing itself *)
Inductive typed : stringmap type → expr → type → Prop :=
  | Var_typed Γ x τ : Γ !! x = Some τ → Γ ⊢ₜ Var x : τ
  | Val_typed Γ v τ :
      ⊢ᵥ v : τ →
      Γ ⊢ₜ Val v : τ
  | Unit_typed Γ :
      Γ ⊢ₜ #() : TUnit
  | Nat_typed Γ (n : nat) :
      Γ ⊢ₜ #n : TNat
  | Bool_typed Γ (b : bool) :
      Γ ⊢ₜ #b : TBool
  | BinOp_typed_nat Γ op e1 e2 τ :
     Γ ⊢ₜ e1 : TNat → Γ ⊢ₜ e2 : TNat →
     binop_nat_res_type op = Some τ →
     Γ ⊢ₜ BinOp op e1 e2 : τ
  | BinOp_typed_bool Γ op e1 e2 τ :
     Γ ⊢ₜ e1 : TBool → Γ ⊢ₜ e2 : TBool →
     binop_bool_res_type op = Some τ →
     Γ ⊢ₜ BinOp op e1 e2 : τ
  | RefEq_typed Γ e1 e2 τ :
     Γ ⊢ₜ e1 : Tref τ → Γ ⊢ₜ e2 : Tref τ →
     Γ ⊢ₜ BinOp EqOp e1 e2 : TBool
  | Pair_typed Γ e1 e2 τ1 τ2 :
      Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 →
      Γ ⊢ₜ (e1, e2) : τ1 * τ2
  | Fst_typed Γ e τ1 τ2 :
      Γ ⊢ₜ e : τ1 * τ2 →
      Γ ⊢ₜ Fst e : τ1
  | Snd_typed Γ e τ1 τ2 :
      Γ ⊢ₜ e : τ1 * τ2 →
      Γ ⊢ₜ Snd e : τ2
  | InjL_typed Γ e τ1 τ2 :
      Γ ⊢ₜ e : τ1 →
      Γ ⊢ₜ InjL e : τ1 + τ2
  | InjR_typed Γ e τ1 τ2 :
      Γ ⊢ₜ e : τ2 →
      Γ ⊢ₜ InjR e : τ1 + τ2
  | Case_typed Γ e0 e1 e2 τ1 τ2 τ3 :
     Γ ⊢ₜ e0 : τ1 + τ2 →
     Γ ⊢ₜ e1 : (τ1 → τ3) →
     Γ ⊢ₜ e2 : (τ2 → τ3) →
     Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed Γ e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool →
     Γ ⊢ₜ e1 : τ →
     Γ ⊢ₜ e2 : τ →
     Γ ⊢ₜ If e0 e1 e2 : τ
  | Rec_typed Γ f x e τ1 τ2 :
     <[f:=(τ1 → τ2)%ty]>(<[x:=τ1]>Γ) ⊢ₜ e : τ2 →
     Γ ⊢ₜ (rec: f x := e) : (τ1 → τ2)
  | App_typed Γ e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : (τ1 → τ2) →
     Γ ⊢ₜ e2 : τ1 →
     Γ ⊢ₜ e1 e2 : τ2
  | TLam_typed Γ e τ :
     ⤉ Γ ⊢ₜ e : τ →
     Γ ⊢ₜ (Λ: e) : ∀: τ
  | TApp_typed Γ e τ τ' :
     Γ ⊢ₜ e : (∀: τ) →
     Γ ⊢ₜ e #() : τ.[τ'/]
  | TFold Γ e τ :
      Γ ⊢ₜ e : τ.[(μ: τ)%ty/] →
      Γ ⊢ₜ e : (μ: τ)
  | TUnfold Γ e τ :
      Γ ⊢ₜ e : (μ: τ)%ty →
      Γ ⊢ₜ rec_unfold e : τ.[(μ: τ)%ty/]
  | TPack Γ e τ τ' :
      Γ ⊢ₜ e : τ.[τ'/] →
      Γ ⊢ₜ e : (∃: τ)
  | TUnpack Γ e1 x e2 τ τ2 :
      Γ ⊢ₜ e1 : (∃: τ) →
      <[x:=τ]>(⤉ Γ) ⊢ₜ e2 : (Autosubst_Classes.subst (ren (+1%nat)) τ2) →
      Γ ⊢ₜ (unpack: x := e1 in e2) : τ2
  | TFork Γ e : Γ ⊢ₜ e : TUnit → Γ ⊢ₜ Fork e : TUnit
  | TAlloc Γ e τ : Γ ⊢ₜ e : τ → Γ ⊢ₜ Alloc e : Tref τ
  | TLoad Γ e τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ Load e : τ
  | TStore Γ e e' τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ e' : τ → Γ ⊢ₜ Store e e' : TUnit
  | TFAA Γ e1 e2 :
     Γ ⊢ₜ e1 : Tref TNat →
     Γ ⊢ₜ e2 : TNat →
     Γ ⊢ₜ FAA e1 e2 : TNat
  | TCmpXchg Γ e1 e2 e3 τ :
     EqType τ → UnboxedType τ →
     Γ ⊢ₜ e1 : Tref τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ e3 : τ →
     Γ ⊢ₜ CmpXchg e1 e2 e3 : TProd τ TBool
with val_typed : val → type → Prop :=
  | Unit_val_typed : ⊢ᵥ #() : TUnit
  | Nat_val_typed (n : nat) : ⊢ᵥ #n : TNat
  | Bool_val_typed (b : bool) : ⊢ᵥ #b : TBool
  | Pair_val_typed v1 v2 τ1 τ2 :
      ⊢ᵥ v1 : τ1 →
      ⊢ᵥ v2 : τ2 →
      ⊢ᵥ PairV v1 v2 : TProd τ1 τ2
  | InjL_val_typed v τ1 τ2 :
      ⊢ᵥ v : τ1 →
      ⊢ᵥ InjLV v : TSum τ1 τ2
  | InjR_val_typed v τ1 τ2 :
      ⊢ᵥ v : τ2 →
      ⊢ᵥ InjRV v : TSum τ1 τ2
  | Rec_val_typed f x e τ1 τ2 :
     <[f:=TArrow τ1 τ2]>(<[x:=τ1]>∅) ⊢ₜ e : τ2 →
     ⊢ᵥ RecV f x e : TArrow τ1 τ2
  | TLam_val_typed e τ :
     ∅ ⊢ₜ e : τ →
     ⊢ᵥ (Λ: e) : TForall τ
where "Γ ⊢ₜ e : τ" := (typed Γ e τ)
and "⊢ᵥ e : τ" := (val_typed e τ).

Lemma binop_nat_typed_safe (op : bin_op) (n1 n2 : Z) τ :
  binop_nat_res_type op = Some τ → is_Some (bin_op_eval op #n1 #n2).
Proof. destruct op; simpl; eauto. discriminate. Qed.

Lemma binop_bool_typed_safe (op : bin_op) (b1 b2 : bool) τ :
  binop_bool_res_type op = Some τ → is_Some (bin_op_eval op #b1 #b2).
Proof. destruct op; naive_solver. Qed.

From stdpp Require Import fin_map_dom.

Lemma typed_is_closed Γ e τ :
  Γ ⊢ₜ e : τ → is_closed_expr (elements (dom stringset Γ)) e
with typed_is_closed_val v τ :
    ⊢ᵥ v : τ → is_closed_val v.
Proof.
  - inversion 1; simpl; try naive_solver.
    + destruct f as [|f], x as [|x]; simpl; first naive_solver.
      * specialize (typed_is_closed (<[x:=τ1]>Γ) e0 τ2 H0).
        revert typed_is_closed. rewrite dom_insert_L.
        admit.
      * admit.
      * admit.
    + specialize (typed_is_closed (⤉Γ) e0 τ0 H0).
      revert typed_is_closed. by rewrite dom_fmap_L.
    + admit.
  - inversion 1; simpl; try naive_solver.
Admitted.
