(* ReLoC -- Relational logic for fine-grained concurrency *)
(** (Syntactic) Typing for System F_mu_ref with existential types and concurrency *)
From Autosubst Require Export Autosubst.
From stdpp Require Export stringmap fin_map_dom gmap.
From iris.heap_lang Require Export lang notation metatheory.

(** * Types *)
Inductive type :=
  | TUnit : type
  | TNat : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec : {bind 1 of type} → type
  | TVar : var → type
  | TForall : {bind 1 of type} → type
  | TExists : {bind 1 of type} → type
  | TRef : type → type.

(** Which types are unboxed -- we can only do CAS on locations which hold unboxed types *)
Inductive UnboxedType : type → Prop :=
  | UnboxedTUnit : UnboxedType TUnit
  | UnboxedTNat : UnboxedType TNat
  | UnboxedTBool : UnboxedType TBool
  | UnboxedTRef τ : UnboxedType (TRef τ).

(** Types which support direct equality test (which coincides with ctx equiv).
    This is an auxiliary notion. *)
Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TNat
  | EqTBool : EqType TBool
  | EqTProd τ τ' : EqType τ → EqType τ' → EqType (TProd τ τ')
  | EqSum τ τ' : EqType τ → EqType τ' → EqType (TSum τ τ').

Lemma unboxed_type_ref_or_eqtype τ :
  UnboxedType τ → (EqType τ ∨ ∃ τ', τ = TRef τ').
Proof. inversion 1; first [ left; by econstructor | right; naive_solver ]. Qed.

(** Autosubst instances *)
Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Definition binop_nat_res_type (op : bin_op) : option type :=
  match op with
  | MultOp => Some TNat | PlusOp => Some TNat | MinusOp => Some TNat
  | EqOp => Some TBool | LeOp => Some TBool | LtOp => Some TBool
  | _ => None
  end.
Definition binop_bool_res_type (op : bin_op) : option type :=
  match op with
  | XorOp => Some TBool | EqOp => Some TBool
  | _ => None
  end.
Definition unop_nat_res_type (op : un_op) : option type :=
  match op with
  | MinusUnOp => Some TNat
  | _ => None
  end.
Definition unop_bool_res_type (op : un_op) : option type :=
  match op with
  | NegOp => Some TBool
  | _ => None
  end.

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with type.
Notation "()" := TUnit : FType_scope.
Notation "# x" := (TVar x) : FType_scope.
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
Notation "'ref' τ" := (TRef τ%ty) (at level 10, τ at next level, right associativity): FType_scope.

(** * Typing judgements *)
Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
Reserved Notation "⊢ᵥ v : τ" (at level 20, v, τ at next level).

(* Shift all the indices in the context by one,
   used when inserting a new type interpretation in Δ. *)
Notation "⤉ Γ" := (Autosubst_Classes.subst (ren (+1)) <$> Γ) (at level 10, format "⤉ Γ").

(** We model type-level lambdas and applications as thunks *)
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing).
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.
Notation "'TApp' e" := (App e%E #()%E) (at level 200, only parsing).

(* To unfold a recursive type, we need to take a step. We thus define the
unfold operator to be the identity function. *)
Definition rec_unfold : val := λ: "x", "x".
Definition unpack : val := λ: "x" "y", "y" "x".

Notation "'unpack:' x := e1 'in' e2" := (unpack e1%E (Lam x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200, only parsing) : expr_scope.

Notation "'unpack:' x := e1 'in' e2" := (unpack e1%E (LamV x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200, only parsing) : val_scope.

(** Operation lifts *)
Instance insert_binder (A : Type): Insert binder A (stringmap A) :=
  binder_insert.

(** Typing itself *)
Inductive typed : stringmap type → expr → type → Prop :=
  | Var_typed Γ x τ :
     Γ !! x = Some τ →
     Γ ⊢ₜ Var x : τ
  | Val_typed Γ v τ :
     ⊢ᵥ v : τ →
     Γ ⊢ₜ Val v : τ
  | BinOp_typed_nat Γ op e1 e2 τ :
     Γ ⊢ₜ e1 : TNat → Γ ⊢ₜ e2 : TNat →
     binop_nat_res_type op = Some τ →
     Γ ⊢ₜ BinOp op e1 e2 : τ
  | BinOp_typed_bool Γ op e1 e2 τ :
     Γ ⊢ₜ e1 : TBool → Γ ⊢ₜ e2 : TBool →
     binop_bool_res_type op = Some τ →
     Γ ⊢ₜ BinOp op e1 e2 : τ
  | UnOp_typed_nat Γ op e τ :
     Γ ⊢ₜ e : TNat →
     unop_nat_res_type op = Some τ →
     Γ ⊢ₜ UnOp op e : τ
  | UnOp_typed_bool Γ op e τ :
     Γ ⊢ₜ e : TBool →
     unop_bool_res_type op = Some τ →
     Γ ⊢ₜ UnOp op e : τ
  | UnboxedEq_typed Γ e1 e2 τ :
     UnboxedType τ →
     Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ →
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
     <[x:=τ]>(⤉ Γ) ⊢ₜ e2 : (Autosubst_Classes.subst (ren (+1)) τ2) →
     Γ ⊢ₜ (unpack: x := e1 in e2) : τ2
  | TFork Γ e : Γ ⊢ₜ e : () → Γ ⊢ₜ Fork e : ()
  | TAlloc Γ e τ : Γ ⊢ₜ e : τ → Γ ⊢ₜ Alloc e : ref τ
  | TLoad Γ e τ : Γ ⊢ₜ e : ref τ → Γ ⊢ₜ Load e : τ
  | TStore Γ e e' τ : Γ ⊢ₜ e : ref τ → Γ ⊢ₜ e' : τ → Γ ⊢ₜ Store e e' : ()
  | TFAA Γ e1 e2 :
     Γ ⊢ₜ e1 : ref TNat →
     Γ ⊢ₜ e2 : TNat →
     Γ ⊢ₜ FAA e1 e2 : TNat
  | TCmpXchg Γ e1 e2 e3 τ :
     UnboxedType τ →
     Γ ⊢ₜ e1 : ref τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ e3 : τ →
     Γ ⊢ₜ CmpXchg e1 e2 e3 : τ * TBool
with val_typed : val → type → Prop :=
  | Unit_val_typed : ⊢ᵥ #() : ()
  | Nat_val_typed (n : nat) : ⊢ᵥ #n : TNat
  | Bool_val_typed (b : bool) : ⊢ᵥ #b : TBool
  | Pair_val_typed v1 v2 τ1 τ2 :
     ⊢ᵥ v1 : τ1 →
     ⊢ᵥ v2 : τ2 →
     ⊢ᵥ PairV v1 v2 : (τ1 * τ2)
  | InjL_val_typed v τ1 τ2 :
     ⊢ᵥ v : τ1 →
     ⊢ᵥ InjLV v : (τ1 + τ2)
  | InjR_val_typed v τ1 τ2 :
     ⊢ᵥ v : τ2 →
     ⊢ᵥ InjRV v : (τ1 + τ2)
  | Rec_val_typed f x e τ1 τ2 :
     <[f:=TArrow τ1 τ2]>(<[x:=τ1]>∅) ⊢ₜ e : τ2 →
     ⊢ᵥ RecV f x e : (τ1 → τ2)
  | TLam_val_typed e τ :
     ∅ ⊢ₜ e : τ →
     ⊢ᵥ (Λ: e) : (∀: τ)
where "Γ ⊢ₜ e : τ" := (typed Γ e τ)
and "⊢ᵥ e : τ" := (val_typed e τ).

Lemma binop_nat_typed_safe (op : bin_op) (n1 n2 : Z) τ :
  binop_nat_res_type op = Some τ → is_Some (bin_op_eval op #n1 #n2).
Proof. destruct op; simpl; eauto. discriminate. Qed.

Lemma binop_bool_typed_safe (op : bin_op) (b1 b2 : bool) τ :
  binop_bool_res_type op = Some τ → is_Some (bin_op_eval op #b1 #b2).
Proof. destruct op; naive_solver. Qed.


Lemma unop_nat_typed_safe (op : un_op) (n : Z) τ :
  unop_nat_res_type op = Some τ → is_Some (un_op_eval op #n).
Proof. destruct op; simpl; eauto.  Qed.

Lemma unop_bool_typed_safe (op : un_op) (b : bool) τ :
  unop_bool_res_type op = Some τ → is_Some (un_op_eval op #b).
Proof. destruct op; naive_solver. Qed.

(***********************************)
(** Closedness of typed programs   *)

(* DF: It is not trivial to prove the closedness theorem by using the
definition of [is_closed_expr] as it is, because it would require (for
one of the cases) a lemma like this:

  elements (dom (<[x:=τ]> Γ)) = x :: elements (dom Γ).

But this does not hold (it holds only up to multiset equality). So we
use an auxiliary definition with sets *)

Definition maybe_insert_binder (x : binder) (X : stringset) : stringset :=
  match x with
  | BAnon => X
  | BNamed f => {[f]} ∪ X
  end.

Local Fixpoint is_closed_expr_set (X : stringset) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val_set v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr_set (maybe_insert_binder f (maybe_insert_binder x X)) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Free e | Load e =>
     is_closed_expr_set X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 | FAA e1 e2 | Xchg e1 e2 =>
     is_closed_expr_set X e1 && is_closed_expr_set X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2 | Resolve e0 e1 e2 =>
     is_closed_expr_set X e0 && is_closed_expr_set X e1 && is_closed_expr_set X e2
  | NewProph => true
  end
with is_closed_val_set (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV f x e => is_closed_expr_set (maybe_insert_binder f (maybe_insert_binder x ∅)) e
  | PairV v1 v2 => is_closed_val_set v1 && is_closed_val_set v2
  | InjLV v | InjRV v => is_closed_val_set v
  end.

Lemma is_closed_expr_permute (e : expr) (xs ys : list string) :
  xs ≡ₚ ys →
  is_closed_expr xs e = is_closed_expr ys e.
Proof.
  revert xs ys. induction e=>xs ys Hxsys /=;
    repeat match goal with
    | [ |- _ && _ = _ && _ ] => f_equal
    | [ H : ∀ xs ys, xs ≡ₚ ys → is_closed_expr xs _ = is_closed_expr ys _
      |- is_closed_expr _ _ = is_closed_expr _ _ ] => eapply H; eauto
    end; try done.
  - apply bool_decide_iff. by rewrite Hxsys.
  - by rewrite Hxsys.
Qed.

Global Instance is_closed_expr_proper : Proper (Permutation ==> eq ==> eq) is_closed_expr.
Proof.
  intros X1 X2 HX x y ->. by eapply is_closed_expr_permute.
Qed.

Lemma is_closed_expr_set_sound (X : stringset) (e : expr) :
  is_closed_expr_set X e → is_closed_expr (elements X) e
with is_closed_val_set_sound (v : val) :
  is_closed_val_set v → is_closed_val v.
Proof.
  - induction e; simplify_eq/=; try by (intros; destruct_and?; split_and?; eauto).
    + intros. case_bool_decide; last done.
      by apply bool_decide_pack, elem_of_elements.
    + destruct f as [|f], x as [|x]; simplify_eq/=.
      * eapply IHe.
      * intros H%is_closed_expr_set_sound.
        eapply is_closed_weaken; eauto. by set_solver.
      * intros H%is_closed_expr_set_sound.
        eapply is_closed_weaken; eauto. by set_solver.
      * intros H%is_closed_expr_set_sound.
        eapply is_closed_weaken; eauto. by set_solver.
  - induction v; simplify_eq/=; try naive_solver.
    destruct f as [|f], x as [|x]; simplify_eq/=;
      intros H%is_closed_expr_set_sound; revert H.
    + set_solver.
    + by rewrite ?right_id_L elements_singleton.
    + by rewrite ?right_id_L elements_singleton.
    + rewrite ?right_id_L.
      intros. eapply is_closed_weaken; eauto.
      destruct (decide (f = x)) as [->|?].
      * rewrite union_idemp_L elements_singleton.
        set_solver.
      * rewrite elements_disj_union; last set_solver.
        rewrite !elements_singleton. set_solver.
Qed.

Local Lemma typed_is_closed_set Γ e τ :
  Γ ⊢ₜ e : τ → is_closed_expr_set (dom stringset Γ) e
with typed_is_closed_val_set v τ :
    ⊢ᵥ v : τ → is_closed_val_set v.
Proof.
  - induction 1; simplify_eq/=; try (split_and?; by eapply typed_is_closed_set).
    + apply bool_decide_pack. apply elem_of_dom. eauto.
    + by eapply typed_is_closed_val_set.
    + destruct f as [|f], x as [|x]; simplify_eq/=.
      * eapply typed_is_closed_set. eauto.
      * specialize (typed_is_closed_set (<[x:=τ1]>Γ) e τ2 H).
        revert typed_is_closed_set. by rewrite dom_insert_L.
      * specialize (typed_is_closed_set (<[f:=(τ1→τ2)%ty]>Γ) e τ2 H).
        revert typed_is_closed_set. by rewrite dom_insert_L.
      * specialize (typed_is_closed_set _ e τ2 H).
        revert typed_is_closed_set.
        rewrite (dom_insert_L (D:=stringset) (<[x:=τ1]> Γ) f (τ1→τ2)%ty).
        by rewrite dom_insert_L.
    + specialize (typed_is_closed_set (⤉Γ) e τ H).
      revert typed_is_closed_set. by rewrite dom_fmap_L.
    + by split_and?.
    + by split_and?.
    + split_and?; eauto. try (apply bool_decide_pack; by set_solver).
      destruct x as [|x]; simplify_eq/=.
      ++ specialize (typed_is_closed_set _ _ _ H0).
         revert typed_is_closed_set. by rewrite dom_fmap_L.
      ++ specialize (typed_is_closed_set _ _ _ H0).
         revert typed_is_closed_set. rewrite (dom_insert_L (D:=stringset) (⤉Γ) x).
         by rewrite dom_fmap_L.
  - induction 1; simplify_eq/=; try done.
    + by split_and?.
    + destruct f as [|f], x as [|x]; simplify_eq/=.
      * specialize (typed_is_closed_set _ _ _ H).
        revert typed_is_closed_set. by rewrite dom_empty_L.
      * specialize (typed_is_closed_set (<[x:=τ1]>∅) _ _ H).
        revert typed_is_closed_set. by rewrite dom_insert_L dom_empty_L.
      * specialize (typed_is_closed_set _ _ _ H).
        revert typed_is_closed_set.
        rewrite (dom_insert_L (D:=stringset) _ f (τ1→τ2)%ty).
        by rewrite dom_empty_L.
      * specialize (typed_is_closed_set _ _ _ H).
        revert typed_is_closed_set.
        rewrite (dom_insert_L (D:=stringset) (<[x:=τ1]> ∅) f (τ1→τ2)%ty).
        by rewrite dom_insert_L dom_empty_L.
    + specialize (typed_is_closed_set _ _ _ H).
      revert typed_is_closed_set. by rewrite dom_empty_L.
Qed.

Theorem typed_is_closed Γ e τ :
  Γ ⊢ₜ e : τ → is_closed_expr (elements (dom stringset Γ)) e.
Proof. intros. eapply is_closed_expr_set_sound, typed_is_closed_set; eauto. Qed.

