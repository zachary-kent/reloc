(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Main ReLoC proofmode files *)
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction.
From reloc.logic Require Import proofmode.spec_tactics.
From reloc.logic Require Export model rules.
From iris.proofmode Require Export tactics.
(* Set Default Proof Using "Type". *)

(** * General-purpose tactics *)
Lemma tac_rel_bind_l `{relocG Σ} e' K ℶ E e t A :
  e = fill K e' →
  envs_entails ℶ (REL fill K e' << t @ E : A) →
  envs_entails ℶ (REL e << t @ E : A).
Proof. intros. subst. assumption. Qed.

Lemma tac_rel_bind_r `{relocG Σ} t' K ℶ E e t A :
  t = fill K t' →
  envs_entails ℶ (REL e << fill K t' @ E : A) →
  envs_entails ℶ (REL e << t @ E : A).
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

Ltac rel_bind_ctx_l K :=
  eapply (tac_rel_bind_l _ K);
  [pm_reflexivity || tp_bind_helper
  |].

Ltac rel_bind_ctx_r K :=
  eapply (tac_rel_bind_r _ K);
  [pm_reflexivity || tp_bind_helper
  |].


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

(** Reshape the expression on the LHS/RHS untill you can apply `tac` to it *)
Ltac rel_reshape_cont_l tac :=
  lazymatch goal with
  | |- envs_entails _ (refines _ (fill ?K ?e) _ _) =>
    reshape_expr e ltac:(fun K' e' =>
      tac (K' ++ K) e')
  | |- envs_entails _ (refines _ ?e _ _) =>
    reshape_expr e ltac:(fun K' e' => tac K' e')
  end.

Ltac rel_reshape_cont_r tac :=
  lazymatch goal with
  | |- envs_entails _ (refines _ _ (fill ?K ?e) _) =>
    reshape_expr e ltac:(fun K' e' =>
      tac (K' ++ K) e')
  | |- envs_entails _ (refines _ _ ?e _) =>
    reshape_expr e ltac:(fun K' e' => tac K' e')
  end.


(** 1. prettify ▷s caused by [MaybeIntoLaterNEnvs]
    2. simplify the goal *)
Ltac rel_finish := pm_prettify; iSimpl.

Ltac rel_values :=
  iStartProof;
  iApply refines_ret;
  eauto with iFrame;
  (* TODO: check that we have actually succeeded in solving the previous conditions, or add rel_pure_l/r beforehand *)
  rel_finish.

Tactic Notation "rel_apply_l" open_constr(lem) :=
  (iPoseProofCore lem as false true (fun H =>
    rel_reshape_cont_l ltac:(fun K e =>
      rel_bind_ctx_l K;
      iApplyHyp H)
    || lazymatch iTypeOf H with
      | Some (_,?P) => fail "rel_apply_l: Cannot apply" P
      end));
  try lazymatch goal with
  | |- val_is_unboxed _ => fast_done
  | |- vals_cas_compare_safe _ _ =>
    fast_done || (left; fast_done) || (right; fast_done)
  end;
  try rel_finish.

Tactic Notation "rel_apply_r" open_constr(lem) :=
  (iPoseProofCore lem as false true (fun H =>
    rel_reshape_cont_r ltac:(fun K e =>
      rel_bind_ctx_r K;
      iApplyHyp H)
    || lazymatch iTypeOf H with
      | Some (_,?P) => fail "rel_apply_r: Cannot apply" P
      end));
  try lazymatch goal with
  | |- _ ⊆ _ => try solve_ndisj
  end;
  try rel_finish.

(** * Symbolic execution *)

(** Pure reductions *)

Lemma tac_rel_pure_l `{relocG Σ} K e1 ℶ ℶ' E e e2 eres ϕ n m t A :
  e = fill K e1 →
  PureExec ϕ n e1 e2 →
  ϕ →
  ((m = n ∧ E = ⊤) ∨ m = 0%nat) →
  MaybeIntoLaterNEnvs m ℶ ℶ' →
  eres = fill K e2 →
  envs_entails ℶ' (REL eres << t @ E : A) →
  envs_entails ℶ (REL e << t @ E : A).
Proof.
  rewrite envs_entails_eq.
  intros Hfill Hpure Hϕ Hm ?? Hp. subst.
  destruct Hm as [[-> ->] | ->]; rewrite into_laterN_env_sound /= Hp.
  - rewrite -refines_pure_l //.
  - rewrite -refines_masked_l //.
Qed.

Lemma tac_rel_pure_r `{relocG Σ} K e1 ℶ E e e2 eres ϕ n t A :
  e = fill K e1 →
  PureExec ϕ n e1 e2 →
  ϕ →
  nclose specN ⊆ E →
  eres = fill K e2 →
  envs_entails ℶ (REL t << eres @ E : A) →
  envs_entails ℶ (REL t << e @ E : A).
Proof.
  intros Hfill Hpure Hϕ ?? Hp. subst.
  rewrite -refines_pure_r //.
Qed.

(* Tactic Notation "rel_pure_l" open_constr(ef) := *)
(*   iStartProof; *)
(*   (eapply tac_rel_pure_l; *)
(*    [tac_bind_helper ef                           (** e = fill K e1' *) *)
(*    |iSolveTC                                     (** PureClosed ϕ n e1 e2 *) *)
(*    |try fast_done                                (** The pure condition for PureClosed *) *)
(*    |first [left; split; reflexivity              (** Here we decide if the mask E is ⊤ *) *)
(*           | right; reflexivity]                  (**    (m = n ∧ E = ⊤) ∨ (m = 0) *) *)
(*    |iSolveTC                                     (** IntoLaters *) *)
(*    |simpl; reflexivity                           (** eres = fill K e2 *) *)
(*    |rel_finish                                   (** new goal *)]) *)
(*   || fail "rel_pure_l: cannot find the reduct". *)

Tactic Notation "rel_pure_l" open_constr(ef) :=
  iStartProof;
  rel_reshape_cont_l ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_rel_pure_l K e');
      [reflexivity                  (** e = fill K e1 *)
      |iSolveTC                     (** PureClosed ϕ e1 e2 *)
      |try fast_done                (** φ *)
      |first [left; split; reflexivity              (** Here we decide if the mask E is ⊤ *)
             | right; reflexivity]                  (**    (m = n ∧ E = ⊤) ∨ (m = 0) *)
      |iSolveTC                                     (** IntoLaters *)
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)])
  || fail "rel_pure_l: cannot find the reduct".

Tactic Notation "rel_pure_l" := rel_pure_l _.

Tactic Notation "rel_pure_r" open_constr(ef) :=
  iStartProof;
  rel_reshape_cont_r ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_rel_pure_r K e');
      [reflexivity                  (** e = fill K e1 *)
      |iSolveTC                     (** PureClosed ϕ e1 e2 *)
      |try fast_done                (** φ *)
      |solve_ndisj        || fail 1 "rel_pure_r: cannot solve ↑specN ⊆ ?"
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)])
  || fail "rel_pure_r: cannot find the reduct".

Tactic Notation "rel_pure_r" := rel_pure_r _.

(** Load *)

Lemma tac_rel_load_l_simp `{relocG Σ} K ℶ1 ℶ2 i1 (l : loc) q v e t eres A :
  e = fill K (Load (# l)) →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  envs_lookup i1 ℶ2 = Some (false, l ↦{q} v)%I →
  eres = fill K (of_val v) →
  envs_entails ℶ2 (refines ⊤ eres t A) →
  envs_entails ℶ1 (refines ⊤ e t A).
Proof.
  rewrite envs_entails_eq. intros ???? Hℶ2; subst.
  rewrite into_laterN_env_sound envs_lookup_split // /=.
  rewrite bi.later_sep. rewrite Hℶ2.
  apply: bi.wand_elim_l' =>/=.
  rewrite -(refines_load_l K ⊤ l q).
  rewrite -fupd_intro.
  rewrite -(bi.exist_intro v).
  by apply bi.wand_intro_r.
Qed.

Lemma tac_rel_load_r `{relocG Σ} K ℶ1 ℶ2 E i1 (l : loc) q e t tres A v :
  t = fill K (Load (# l)) →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ{q} v)%I →
  (* TODO: the line below is a detour! *)
  envs_simple_replace i1 false
    (Esnoc Enil i1 (l ↦ₛ{q} v)%I) ℶ1 = Some ℶ2 →
  tres = fill K (of_val v) →
  envs_entails ℶ2 (refines E e tres A) →
  envs_entails ℶ1 (refines E e t A).
Proof.
  rewrite envs_entails_eq. intros ????? Hg.
  rewrite (envs_simple_replace_sound ℶ1 ℶ2 i1) //; simpl.
  rewrite right_id.
  subst t tres.
  rewrite {1}(refines_load_r E); [ | eassumption ].
  rewrite Hg.
  apply bi.wand_elim_l.
Qed.

Tactic Notation "rel_load_l" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "rel_load_l: cannot find" l "↦ ?" in
  iStartProof;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_load_l_simp K); first reflexivity)
    |fail 1 "rel_load_l: cannot find 'Load'"];
  (* the remaining goals are from tac_lel_load_l (except for the first one, which has already been solved by this point) *)
  [iSolveTC             (** IntoLaters *)
  |solve_mapsto ()
  |reflexivity       (** eres = fill K v *)
  |rel_finish  (** new goal *)].

Tactic Notation "rel_load_l_atomic" := rel_apply_l refines_load_l.

(* The structure for the tacticals on the right hand side is a bit
different. Because there is only one type of rules, we can report
errors in a more precise way. E.g. if we are executing !#l and l ↦ₛ is
not found in the environment, then we can immediately fail with an
error *)
Tactic Notation "rel_load_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ{_} _)%I) => l end in
    iAssumptionCore || fail "rel_load_r: cannot find" l "↦ₛ ?" in
  iStartProof;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_load_r K); first reflexivity)
    |fail 1 "rel_load_r: cannot find 'Load'"];
  (* the remaining goals are from tac_rel_load_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_load_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |pm_reflexivity || fail "rel_load_r: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].

(** Store *)
Lemma tac_rel_store_l_simpl `{relocG Σ} K ℶ1 ℶ2 ℶ3 i1 (l : loc) v e' v' e t eres A :
  e = fill K (Store (# l) e') →
  IntoVal e' v' →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  envs_lookup i1 ℶ2 = Some (false, l ↦ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ v')) ℶ2 = Some ℶ3 →
  eres = fill K #() →
  envs_entails ℶ3 (refines ⊤ eres t A) →
  envs_entails ℶ1 (refines ⊤ e t A).
Proof.
  rewrite envs_entails_eq. intros ?????? Hg.
  subst e eres.
  rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
  rewrite bi.later_sep.
  rewrite right_id.
  rewrite -(refines_store_l K ⊤ l).
  rewrite -fupd_intro.
  rewrite -(bi.exist_intro v).
  by rewrite Hg.
Qed.

Lemma tac_rel_store_r `{relocG Σ} K ℶ1 ℶ2 i1 E (l : loc) v e' v' e t eres A :
  e = fill K (Store (# l) e') →
  IntoVal e' v' →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ₛ v')) ℶ1 = Some ℶ2 →
  eres = fill K #() →
  envs_entails ℶ2 (refines E t eres A) →
  envs_entails ℶ1 (refines E t e A).
Proof.
  rewrite envs_entails_eq. intros ?????? Hg.
  subst e eres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite (refines_store_r E K) //.
  rewrite Hg.
  apply bi.wand_elim_l.
Qed.

Tactic Notation "rel_store_l" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ _)%I) => l end in
    iAssumptionCore || fail "rel_store_l: cannot find" l "↦ₛ ?" in
  iStartProof;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_store_l_simpl K);
       [reflexivity (** e = fill K (#l <- e') *)
       |iSolveTC    (** e' is a value *)
       |idtac..])
    |fail 1 "rel_store_l: cannot find 'Store'"];
  (* the remaining goals are from tac_rel_store_l (except for the first one, which has already been solved by this point) *)
  [iSolveTC        (** IntoLaters *)
  |solve_mapsto ()
  |pm_reflexivity || fail "rel_store_l: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].

Tactic Notation "rel_store_l_atomic" := rel_apply_l refines_store_l.

Tactic Notation "rel_store_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ _)%I) => l end in
    iAssumptionCore || fail "rel_store_r: cannot find" l "↦ₛ ?" in
  iStartProof;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_store_r K);
       [reflexivity|iSolveTC|idtac..])
    |fail 1 "rel_store_r: cannot find 'Store'"];
  (* the remaining goals are from tac_rel_store_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_store_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |pm_reflexivity || fail "rel_store_r: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].

(** Alloc *)
Tactic Notation "rel_alloc_l_atomic" := rel_apply_l refines_alloc_l.

Lemma tac_rel_alloc_l_simpl `{relocG Σ} K ℶ1 ℶ2 e t e' v' A :
  e = fill K (Alloc e') →
  IntoVal e' v' →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  (envs_entails ℶ2 (∀ (l : loc),
     (l ↦ v' -∗ refines ⊤ (fill K (of_val #l)) t A))) →
  envs_entails ℶ1 (refines ⊤ e t A).
Proof.
  rewrite envs_entails_eq. intros ???; subst.
  rewrite into_laterN_env_sound /=.
  rewrite -(refines_alloc_l _ ⊤); eauto.
  rewrite -fupd_intro.
  apply bi.later_mono.
Qed.

Tactic Notation "rel_alloc_l" ident(l) "as" constr(H) :=
  iStartProof;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_alloc_l_simpl K);
       [reflexivity (** e = fill K (Alloc e') *)
       |iSolveTC    (** e' is a value *)
       |idtac..])
    |fail 1 "rel_alloc_l: cannot find 'Alloc'"];
  [iSolveTC        (** IntoLaters *)
  |iIntros (l) H; rel_finish  (** new goal *)].

Lemma tac_rel_alloc_r `{relocG Σ} K' ℶ E t' v' e t A :
  t = fill K' (Alloc t') →
  IntoVal t' v' →
  nclose specN ⊆ E →
  envs_entails ℶ (∀ l, l ↦ₛ v' -∗ refines E e (fill K' #l) A) →
  envs_entails ℶ (refines E e t A).
Proof.
  intros ????. subst t.
  rewrite -refines_alloc_r //.
Qed.

Tactic Notation "rel_alloc_r" ident(l) "as" constr(H) :=
  iStartProof;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_alloc_r K);
       [reflexivity  (** t = K'[alloc t'] *)
       |iSolveTC     (** t' is a value *)
       |idtac..])
    |fail 1 "rel_alloc_r: cannot find 'Alloc'"];
  [solve_ndisj || fail "rel_alloc_r: cannot prove 'nclose specN ⊆ ?'"
  |iIntros (l) H; rel_finish  (** new goal *)].

Tactic Notation "rel_alloc_r" :=
  let l := fresh in
  let H := iFresh "H" in
  rel_alloc_r l as H.

Tactic Notation "rel_alloc_l" :=
  let l := fresh in
  let H := iFresh "H" in
  rel_alloc_l l as H.

(** Cas *)
(* TODO: non-atomic tactics for CAS? *)
Tactic Notation "rel_cas_l_atomic" := rel_apply_l refines_cas_l.

Lemma tac_rel_cas_fail_r `{relocG Σ} K ℶ1 i1 E (l : loc) e1 e2 v1 v2 v e t eres A :
  e = fill K (CAS (# l) e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ v)%I →
  v ≠ v1 →
  vals_cas_compare_safe v v1 →
  eres = fill K #false →
  envs_entails ℶ1 (refines E t eres A) →
  envs_entails ℶ1 (refines E t e A).
Proof.
  rewrite envs_entails_eq. intros ???????? Hg.
  subst e eres.
  rewrite envs_lookup_split // /= Hg; simpl.
  apply bi.wand_elim_l'.
  eapply refines_cas_fail_r; eauto.
Qed.

Lemma tac_rel_cas_suc_r `{relocG Σ} K ℶ1 ℶ2 i1 E (l : loc) e1 e2 v1 v2 v e t eres A :
  e = fill K (CAS (# l) e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ v)%I →
  v = v1 →
  val_is_unboxed v1 →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ₛ v2)) ℶ1 = Some ℶ2 →
  eres = fill K #true →
  envs_entails ℶ2 (refines E t eres A) →
  envs_entails ℶ1 (refines E t e A).
Proof.
  rewrite envs_entails_eq. intros ????????? Hg.
  subst e eres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id Hg.
  apply bi.wand_elim_l'.
  eapply refines_cas_suc_r; eauto.
Qed.

Tactic Notation "rel_cas_fail_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ _)%I) => l end in
    iAssumptionCore || fail "rel_cas_fail_r: cannot find" l "↦ₛ ?" in
  iStartProof;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_cas_fail_r K);
       [reflexivity  (** e = fill K (CAS #l e1 e2) *)
       |iSolveTC     (** e1 is a value *)
       |iSolveTC     (** e2 is a value *)
       |idtac..])
    |fail 1 "rel_cas_fail_r: cannot find 'Cas'"];
  (* the remaining goals are from tac_rel_cas_fail_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_cas_fail_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |try congruence   (** v ≠ v1 *)
  |try (fast_done || (left; fast_done) || (right; fast_done)) (** vals_cas_compare_safe *)
  |reflexivity
  |rel_finish  (** new goal *)].

Tactic Notation "rel_cas_suc_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ _)%I) => l end in
    iAssumptionCore || fail "rel_cas_suc_r: cannot find" l "↦ₛ ?" in
  iStartProof;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_cas_suc_r K);
       [reflexivity  (** e = fill K (CAS #l e1 e2) *)
       |iSolveTC     (** e1 is a value *)
       |iSolveTC     (** e2 is a value *)
       |idtac..])
    |fail 1 "rel_cas_suc_r: cannot find 'Cas'"];
  (* the remaining goals are from tac_rel_cas_suc_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_cas_suc_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |try congruence   (** v = v1 *)
  |try fast_done (** val_is_unboxed *)
  |pm_reflexivity  (** new env *)
  |reflexivity
  |rel_finish  (** new goal *)].


(** Fork *)
Lemma tac_rel_fork_l `{relocG Σ} K ℶ E e' eres e t A :
  e = fill K (Fork e') →
  is_closed_expr [] e' →
  eres = fill K #() →
  envs_entails ℶ (|={⊤,E}=> ▷ (WP e' {{ _ , True%I }} ∗ refines E eres t A))%I →
  envs_entails ℶ (refines ⊤ e t A).
Proof.
  intros ????. subst e eres.
  rewrite -refines_fork_l //.
Qed.

Tactic Notation "rel_fork_l" :=
  iStartProof;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_fork_l K); first reflexivity)
    |fail 1 "rel_fork_l: cannot find 'Fork'"];
  (* the remaining goals are from tac_rel_load_r (except for the first one, which has already been solved by this point) *)
  [try fast_done    (** is_closed_expr [] e' *)
  |reflexivity    || fail "rel_fork_l: this should not happen O-:"
  |rel_finish  (** new goal *)].

Lemma tac_rel_fork_r `{relocG Σ} K ℶ E e' e t eres A :
  e = fill K (Fork e') →
  nclose specN ⊆ E →
  is_closed_expr [] e' →
  eres = fill K #() →
  envs_entails ℶ (∀ i, i ⤇ e' -∗ refines E t eres A) →
  envs_entails ℶ (refines E t e A).
Proof.
  intros ?????. subst e eres.
  rewrite -refines_fork_r //.
Qed.

Tactic Notation "rel_fork_r" ident(i) "as" constr(H) :=
  iStartProof;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_fork_r K); first reflexivity)
    |fail 1 "rel_fork_r: cannot find 'Fork'"];
  (* the remaining goals are from tac_rel_load_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_fork_r: cannot prove 'nclose specN ⊆ ?'"
  |try fast_done    (** is_closed_expr [] e' *)
  |reflexivity    || fail "rel_fork_r: this should not happen O-:"
  |iIntros (i) H; rel_finish  (** new goal *)].


(* The handling of beta-reductions is special because it also unlocks
 the locked `RecV` values. The the comments for the `wp_rec` tactic in
 the heap_lang
 proofmode.
 *)
Tactic Notation "rel_rec_l" :=
  let H := fresh in
  assert (H := AsRecV_recv_locked);
  rel_pure_l (App _ _);
  clear H.
Tactic Notation "rel_rec_r" :=
  let H := fresh in
  assert (H := AsRecV_recv_locked);
  rel_pure_r (App _ _);
  clear H.

(** For backwards compatibility *)
Tactic Notation "rel_seq_l" := rel_pure_l (App _ _).
Tactic Notation "rel_let_l" := rel_pure_l (App _ _).
Tactic Notation "rel_fst_l" := rel_pure_l (Fst _).
Tactic Notation "rel_snd_l" := rel_pure_l (Snd _).
Tactic Notation "rel_proj_l" := rel_pure_l (_ (Val (PairV _ _))).
Tactic Notation "rel_case_inl_l" := rel_pure_l (Case _ _ _).
Tactic Notation "rel_case_inr_l" := rel_pure_l (Case _ _ _).
Tactic Notation "rel_case_l" := rel_pure_l (Case _ _ _).
Tactic Notation "rel_binop_l" := rel_pure_l (BinOp _ _ _).
Tactic Notation "rel_op_l" := rel_binop_l.
Tactic Notation "rel_if_true_l" := rel_pure_l (If #true _ _).
Tactic Notation "rel_if_false_l" := rel_pure_l (If #false _ _).
Tactic Notation "rel_if_l" := rel_pure_l (If _ _ _).

Tactic Notation "rel_seq_r" := rel_pure_r (App _ _).
Tactic Notation "rel_let_r" := rel_pure_r (App _ _).
Tactic Notation "rel_fst_r" := rel_pure_r (Fst _).
Tactic Notation "rel_snd_r" := rel_pure_r (Snd _).
Tactic Notation "rel_proj_r" := rel_pure_r (_ (Val (PairV _ _))).
Tactic Notation "rel_case_inl_r" := rel_pure_r (Case _ _ _).
Tactic Notation "rel_case_inr_r" := rel_pure_r (Case _ _ _).
Tactic Notation "rel_case_r" := rel_pure_r (Case _ _ _).
Tactic Notation "rel_binop_r" := rel_pure_r (BinOp _ _ _).
Tactic Notation "rel_op_r" := rel_binop_r.
Tactic Notation "rel_if_true_r" := rel_pure_r (If #true _ _).
Tactic Notation "rel_if_false_r" := rel_pure_r (If #false _ _).
Tactic Notation "rel_if_r" := rel_pure_r (If _ _ _).
