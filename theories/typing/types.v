(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Typing for System F_mu_ref with existential types and concurrency *)
From stdpp Require Export stringmap.
From iris.heap_lang Require Export lang notation.
From Autosubst Require Import Autosubst.

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

Delimit Scope FType_scope with F.
Bind Scope FType_scope with type.
Infix "×" := TProd (at level 80) : FType_scope.
Notation "(×)" := TProd (only parsing) : FType_scope.
Infix "+" := TSum : FType_scope.
Notation "(+)" := TSum (only parsing) : FType_scope.
Infix "→" := TArrow : FType_scope.
Notation "(→)" := TArrow (only parsing) : FType_scope.
Notation "μ: τ" :=
  (TRec τ%F)
  (at level 100, τ at level 200) : FType_scope.
Notation "∀: τ" :=
  (TForall τ%F)
  (at level 100, τ at level 200) : FType_scope.
Notation "∃: τ" :=
  (TExists τ%F)
  (at level 100, τ at level 200) : FType_scope.
Notation "'ref' τ" := (Tref τ%F) (at level 30, right associativity): FType_scope.

(** * Typing judgements *)
Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

(** We model type-level lambdas and applications as thunks *)
Notation "Λ: e" := (λ: <>, e)%E (at level 200).
Notation "'TApp' e" := (App e%E #()%E) (at level 200).

(* To unfold a recursive type, we need to take a step. We thus define the
unfold operator to be the identity function. *)
Definition rec_unfold : val := λ: "x", "x".
Definition unpack : val := λ: "x" "y", "y" "x".

(** Operation lifts *)
Instance insert_binder (A : Type): Insert binder A (stringmap A) :=
  fun k τ Γ =>
    match k with
    | BAnon => Γ
    | BNamed x => <[x:=τ]>Γ
    end.

(** Typing itself *)
Inductive typed (Γ : stringmap type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ₜ Var x : τ
  | Unit_typed : Γ ⊢ₜ #() : TUnit
  | Nat_typed (n : nat) : Γ ⊢ₜ # n : TNat
  | Bool_typed (b : bool) : Γ ⊢ₜ # b : TBool
  | BinOp_typed_nat op e1 e2 τ :
     Γ ⊢ₜ e1 : TNat → Γ ⊢ₜ e2 : TNat →
     binop_nat_res_type op = Some τ →
     Γ ⊢ₜ BinOp op e1 e2 : τ
  | BinOp_typed_bool op e1 e2 τ :
     Γ ⊢ₜ e1 : TBool → Γ ⊢ₜ e2 : TBool →
     binop_bool_res_type op = Some τ →
     Γ ⊢ₜ BinOp op e1 e2 : τ
  | RefEq_typed e1 e2 τ :
     Γ ⊢ₜ e1 : Tref τ → Γ ⊢ₜ e2 : Tref τ →
     Γ ⊢ₜ BinOp EqOp e1 e2 : TBool
  | Pair_typed e1 e2 τ1 τ2 : Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 : Γ ⊢ₜ e : τ1 → Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Γ ⊢ₜ e : τ2 → Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 τ3 :
     Γ ⊢ₜ e0 : TSum τ1 τ2 →
     Γ ⊢ₜ e1 : TArrow τ1 τ3 →
     Γ ⊢ₜ e2 : TArrow τ2 τ3 →
     Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ If e0 e1 e2 : τ
  | Rec_typed f x e τ1 τ2 :
     <[x:=τ1]>(<[f:=TArrow τ1 τ2]>Γ) ⊢ₜ e : τ2 →
     Γ ⊢ₜ Rec f x e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2
  | TLam_typed e τ :
     subst (ren (+1%nat)) <$> Γ ⊢ₜ e : τ →
     Γ ⊢ₜ (Λ: e) : TForall τ
  | TApp_typed e τ τ' : Γ ⊢ₜ e : TForall τ →
     Γ ⊢ₜ e #() : τ.[τ'/]
  | TFold e τ : Γ ⊢ₜ e : τ.[TRec τ/] → Γ ⊢ₜe : TRec τ
  | TUnfold e τ : Γ ⊢ₜ e : TRec τ → Γ ⊢ₜ rec_unfold e : τ.[TRec τ/]
  | TPack e τ τ' : Γ ⊢ₜ e : τ.[τ'/] → Γ ⊢ₜ e : TExists τ
  | TUnpack e1 e2 τ τ2 : Γ ⊢ₜ e1 : TExists τ →
      (subst (ren (+1%nat)) <$> Γ) ⊢ₜ e2 : TArrow τ (subst (ren (+1%nat)) τ2) →
      Γ ⊢ₜ unpack e1 e2 : τ2
  | TFork e : Γ ⊢ₜ e : TUnit → Γ ⊢ₜ Fork e : TUnit
  | TAlloc e τ : Γ ⊢ₜ e : τ → Γ ⊢ₜ Alloc e : Tref τ
  | TLoad e τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ Load e : τ
  | TStore e e' τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ e' : τ → Γ ⊢ₜ Store e e' : TUnit
  | TCAS e1 e2 e3 τ :
     EqType τ → Γ ⊢ₜ e1 : Tref τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ e3 : τ →
     Γ ⊢ₜ CAS e1 e2 e3 : TBool
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).
