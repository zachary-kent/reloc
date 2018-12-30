(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Main ReLoC proofmode files *)
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction.
From reloc.logic Require Import proofmode.spec_tactics.
From reloc.logic Require Export model rules.
(* Set Default Proof Using "Type". *)

(** * General-purpose tactics *)
Lemma tac_rel_bind_l `{relocG Σ} e' K ℶ E Γ e t A :
  e = fill K e' →
  envs_entails ℶ ({E;Γ} ⊨ fill K e' << t : A) →
  envs_entails ℶ ({E;Γ} ⊨ e << t : A).
Proof. intros. subst. assumption. Qed.

Lemma tac_rel_bind_r `{relocG Σ} t' K ℶ E Γ e t A :
  t = fill K t' →
  envs_entails ℶ ({E;Γ} ⊨ e << fill K t' : A) →
  envs_entails ℶ ({E;Γ} ⊨ e << t : A).
Proof. intros. subst. assumption. Qed.

Tactic Notation "rel_bind_l" open_constr(efoc) :=
  iStartProof;
  eapply (tac_rel_bind_l efoc);
  [ tp_bind_helper
  | (* new goal *)
  ].

Tactic Notation "rel_bind_r" open_constr(efoc) :=
  iStartProof;
  eapply (tac_rel_bind_r efoc);
  [ tp_bind_helper
  | (* new goal *)
  ].

(** Similar to `tp_bind_helper`, but tries tries to solve goals for a _specific_ `efoc` *)
Tactic Notation "tac_bind_helper" open_constr(efoc) :=
  lazymatch goal with
  | |- fill ?K ?e = fill _ _ =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ _ =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.

(** Reshape the expression on the RHS untill you can apply `tac` to it *)
Ltac rel_reshape_cont_r tac :=
  lazymatch goal with
  | |- envs_entails _ (refines _ _ _ (fill ?K ?e) _) =>
    reshape_expr e ltac:(fun K' e' =>
      tac (K' ++ K) e')
  | |- envs_entails _ (refines _ _ _ ?e _) =>
    reshape_expr e ltac:(fun K' e' => tac K' e')
  end.


(* prettify ▷s caused by [MaybeIntoLaterNEnvs] *)
Ltac rel_finish := pm_prettify.

Ltac rel_values :=
  iStartProof;
  iApply refines_ret;
  eauto with iFrame;
  rel_finish.

(** TODO: rel_apply_(l/r) *)

(** * Symbolic execution *)

(** Pure reductions *)

Lemma tac_rel_pure_l `{relocG Σ} K e1 ℶ ℶ' E Γ e e2 eres ϕ n m t A :
  e = fill K e1 →
  PureExec ϕ n e1 e2 →
  ϕ →
  ((m = n ∧ E = ⊤) ∨ m = 0%nat) →
  MaybeIntoLaterNEnvs m ℶ ℶ' →
  eres = fill K e2 →
  envs_entails ℶ' ({E;Γ} ⊨ eres << t : A) →
  envs_entails ℶ ({E;Γ} ⊨ e << t : A).
Proof.
  rewrite envs_entails_eq.
  intros Hfill Hpure Hϕ Hm ?? Hp. subst.
  destruct Hm as [[-> ->] | ->]; rewrite into_laterN_env_sound /= Hp.
  - rewrite -refines_pure_l //.
  - rewrite -refines_masked_l //.
Qed.

Lemma tac_rel_pure_r `{relocG Σ} K e1 ℶ E Γ e e2 eres ϕ n t A :
  e = fill K e1 →
  PureExec ϕ n e1 e2 →
  ϕ →
  nclose specN ⊆ E →
  eres = fill K e2 →
  envs_entails ℶ ({E;Γ} ⊨ t << eres : A) →
  envs_entails ℶ ({E;Γ} ⊨ t << e : A).
Proof.
  intros Hfill Hpure Hϕ ?? Hp. subst.
  rewrite -refines_pure_r //.
Qed.

Tactic Notation "rel_pure_l" open_constr(ef) :=
  iStartProof;
  (eapply tac_rel_pure_l;
   [tac_bind_helper ef                           (** e = fill K e1' *)
   |iSolveTC                                     (** PureExec ϕ n e1 e2 *)
   |try fast_done                                (** The pure condition for PureExec *)
   |first [left; split; reflexivity              (** Here we decide if the mask E is ⊤ *)
          | right; reflexivity]                  (**    (m = n ∧ E = ⊤) ∨ (m = 0) *)
   |iSolveTC                                     (** IntoLaters *)
   |simpl; reflexivity                           (** eres = fill K e2 *)
   |rel_finish                                   (** new goal *)])
  || fail "rel_pure_l: cannot find the reduct".

Tactic Notation "rel_pure_l" := rel_pure_l _.

(* Tactic Notation "rel_pure_r" open_constr(ef) := *)
(*   iStartProof; *)
(*   (eapply tac_rel_pure_r; *)
(*    [tac_bind_helper ef                           (** e = fill K e1' *) *)
(*    |iSolveTC                                     (** PureExec ϕ n e1 e2 *) *)
(*    |try fast_done                                (** The pure condition for PureExec *) *)
(*    |solve_ndisj || fail "rel_pure_r: cannot solve ↑specN ⊆ ?" *)
(*    |simpl; reflexivity                           (** eres = fill K e2 *) *)
(*    |rel_finish                                   (** new goal *)]) *)
(*   || fail "rel_pure_r: cannot find the reduct". *)

Tactic Notation "rel_pure_r" open_constr(ef) :=
  iStartProof;
  rel_reshape_cont_r ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_rel_pure_r K e');
      [reflexivity                  (** e = fill K e1 *)
      |iSolveTC                     (** PureExec ϕ e1 e2 *)
      |try fast_done                (** φ *)
      |solve_ndisj        || fail 1 "rel_pure_r: cannot solve ↑specN ⊆ ?"
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)])
  || fail "rel_pure_r: cannot find the reduct".

Tactic Notation "rel_pure_r" := rel_pure_r _.
