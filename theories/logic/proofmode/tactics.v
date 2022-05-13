(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Main ReLoC proofmode files *)
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction.
From reloc.logic Require Import proofmode.spec_tactics.
From reloc.logic Require Export model rules derived.
From iris.proofmode Require Export proofmode.
(* Set Default Proof Using "Type". *)

(** * General-purpose tactics *)
Lemma tac_rel_bind_l `{!relocG Σ} e' K ℶ E e t A :
  e = fill K e' →
  envs_entails ℶ (REL fill K e' << t @ E : A) →
  envs_entails ℶ (REL e << t @ E : A).
Proof. intros. subst. assumption. Qed.

Lemma tac_rel_bind_r `{!relocG Σ} (t' : expr) K ℶ E e t A :
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
  | |- envs_entails _ (refines _ _ (in_1 (fill ?K ?e)) _) =>
    reshape_expr e ltac:(fun K' e' =>
      tac (K' ++ K) e')
  | |- envs_entails _ (refines _ _ (in_1 ?e) _) =>
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
  (iPoseProofCore lem as false (fun H =>
    rel_reshape_cont_l ltac:(fun K e =>
      rel_bind_ctx_l K;
      iApplyHyp H)
    || lazymatch iTypeOf H with
      | Some (_,?P) => fail "rel_apply_l: Cannot apply" P
      end));
  try lazymatch goal with
  | |- val_is_unboxed _ => fast_done
  | |- vals_compare_safe _ _ =>
    fast_done || (left; fast_done) || (right; fast_done)
  end;
  try rel_finish.

Tactic Notation "rel_apply_r" open_constr(lem) :=
  (iPoseProofCore lem as false (fun H =>
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

Lemma tac_rel_pure_l `{!relocG Σ} K e1 ℶ ℶ' E e e2 eres ϕ n m t A :
  e = fill K e1 →
  PureExec ϕ n e1 e2 →
  ϕ →
  ((m = n ∧ E = ⊤) ∨ m = 0) →
  MaybeIntoLaterNEnvs m ℶ ℶ' →
  eres = fill K e2 →
  envs_entails ℶ' (REL eres << t @ E : A) →
  envs_entails ℶ (REL e << t @ E : A).
Proof.
  rewrite envs_entails_unseal.
  intros Hfill Hpure Hϕ Hm ?? Hp. subst.
  destruct Hm as [[-> ->] | ->]; rewrite into_laterN_env_sound /= Hp.
  - rewrite -refines_pure_l //.
  - rewrite -refines_masked_l //.
Qed.

Lemma tac_rel_pure_r `{!relocG Σ} K e1 ℶ E (e e2 eres : expr) ϕ n t A :
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

Tactic Notation "rel_pure_l" open_constr(ef) :=
  iStartProof;
  rel_reshape_cont_l ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_rel_pure_l K e');
      [reflexivity                  (** e = fill K e' *)
      |iSolveTC                     (** PureClosed ϕ e' e2 *)
      | .. ]);
      [try heap_lang.proofmode.solve_vals_compare_safe                (** φ *)
      |first [left; split; reflexivity              (** Here we decide if the mask E is ⊤ *)
             | right; reflexivity]                  (**    (m = n ∧ E = ⊤) ∨ (m = 0) *)
      |iSolveTC                                     (** IntoLaters *)
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)]
  || fail "rel_pure_l: cannot find the reduct".

Tactic Notation "rel_pure_l" := rel_pure_l _.

Tactic Notation "rel_pure_r" open_constr(ef) :=
  iStartProof;
  rel_reshape_cont_r ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_rel_pure_r K e');
      [reflexivity                  (** e = fill K e1 *)
      |iSolveTC                     (** PureClosed ϕ e1 e2 *)
      |..]);
      [try heap_lang.proofmode.solve_vals_compare_safe                (** φ *)
      |solve_ndisj        || fail 1 "rel_pure_r: cannot solve ↑specN ⊆ ?"
      |simpl; reflexivity           (** eres = fill K e2 *)
      |rel_finish                   (** new goal *)]
  || fail "rel_pure_r: cannot find the reduct".

Tactic Notation "rel_pure_r" := rel_pure_r _.

(* TODO: do this in one go, without [repeat]. *)
Ltac rel_pures_l :=
  iStartProof;
  repeat (rel_pure_l _; []). (* The `;[]` makes sure that no side-condition
                             magically spawns. *)
Ltac rel_pures_r :=
  iStartProof;
  repeat (rel_pure_r _; []).

(** Load *)

Lemma tac_rel_load_l_simp `{!relocG Σ} K ℶ1 ℶ2 i1 p (l : loc) q v e t eres A :
  e = fill K (Load (# l)) →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  envs_lookup i1 ℶ2 = Some (p, l ↦{q} v)%I →
  eres = fill K (of_val v) →
  envs_entails ℶ2 (refines ⊤ eres t A) →
  envs_entails ℶ1 (refines ⊤ e t A).
Proof.
  rewrite envs_entails_unseal. iIntros (-> ?? -> Hℶ2) "Henvs".
  iDestruct (into_laterN_env_sound with "Henvs") as "Henvs".
  iDestruct (envs_lookup_split with "Henvs") as "[Hl Henvs]"; first done.
  rewrite Hℶ2. iApply (refines_load_l K ⊤ l q). iModIntro. iExists v.
  destruct p; simpl; [|by iFrame].
  iDestruct "Hl" as "#Hl". iSplitR; [by auto|].
  iIntros "!> _". by iApply "Henvs".
Qed.

Lemma tac_rel_load_r `{!relocG Σ} K ℶ1 E i1 p (l : loc) q e t tres A v :
  t = fill K (Load (# l)) →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (p, l ↦ₛ{q} v)%I →
  tres = fill K (of_val v) →
  envs_entails ℶ1 (refines E e tres A) →
  envs_entails ℶ1 (refines E e t A).
Proof.
  rewrite envs_entails_unseal. iIntros (-> ?? -> Hg) "Henvs".
  iDestruct (envs_lookup_split with "Henvs") as "[Hl Henvs]"; first done.
  rewrite Hg. destruct p; simpl.
  - iDestruct "Hl" as "#Hl". iApply (refines_load_r with "Hl"); first done.
    iIntros "_". by iApply "Henvs".
  - by iApply (refines_load_r with "Hl").
Qed.

Tactic Notation "rel_load_l" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "rel_load_l: cannot find" l "↦ ?" in
  rel_pures_l;
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
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_load_r K); first reflexivity)
    |fail 1 "rel_load_r: cannot find 'Load'"];
  (* the remaining goals are from tac_rel_load_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_load_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |reflexivity
  |rel_finish  (** new goal *)].

(** Store *)
Lemma tac_rel_store_l_simpl `{!relocG Σ} K ℶ1 ℶ2 ℶ3 i1 (l : loc) v e' v' e t eres A :
  e = fill K (Store (# l) e') →
  IntoVal e' v' →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  envs_lookup i1 ℶ2 = Some (false, l ↦ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ v')) ℶ2 = Some ℶ3 →
  eres = fill K #() →
  envs_entails ℶ3 (refines ⊤ eres t A) →
  envs_entails ℶ1 (refines ⊤ e t A).
Proof.
  rewrite envs_entails_unseal. intros ?????? Hg.
  subst e eres.
  rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
  rewrite bi.later_sep.
  rewrite right_id.
  rewrite -(refines_store_l K ⊤ l).
  rewrite -fupd_intro.
  rewrite -(bi.exist_intro v).
  by rewrite Hg.
Qed.

Lemma tac_rel_store_r `{!relocG Σ} K ℶ1 ℶ2 i1 E (l : loc) v e' v' e t eres A :
  e = fill K (Store (# l) e') →
  IntoVal e' v' →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ₛ v')) ℶ1 = Some ℶ2 →
  eres = fill K #() →
  envs_entails ℶ2 (refines E t eres A) →
  envs_entails ℶ1 (refines E t e A).
Proof.
  rewrite envs_entails_unseal. intros ?????? Hg.
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
  rel_pures_l;
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
  rel_pures_r;
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

(** Xchg *)
Lemma tac_rel_xchg_l_simpl `{!relocG Σ} K ℶ1 ℶ2 ℶ3 i1 (l : loc) v e' v' e t eres A :
  e = fill K (Xchg (# l) e') →
  IntoVal e' v' →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  envs_lookup i1 ℶ2 = Some (false, l ↦ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ v')) ℶ2 = Some ℶ3 →
  eres = fill K (of_val v) →
  envs_entails ℶ3 (refines ⊤ eres t A) →
  envs_entails ℶ1 (refines ⊤ e t A).
Proof.
  rewrite envs_entails_unseal. intros ?????? Hg.
  subst e eres.
  rewrite into_laterN_env_sound envs_simple_replace_sound //; simpl.
  rewrite bi.later_sep.
  rewrite right_id.
  rewrite -(refines_xchg_l K ⊤ l).
  rewrite -fupd_intro.
  rewrite -(bi.exist_intro v).
  by rewrite Hg.
Qed.

Lemma tac_rel_xchg_r `{!relocG Σ} K ℶ1 ℶ2 i1 E (l : loc) v e' v' e t eres A :
  e = fill K (Xchg (# l) e') →
  IntoVal e' v' →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ v)%I →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ₛ v')) ℶ1 = Some ℶ2 →
  eres = fill K (of_val v) →
  envs_entails ℶ2 (refines E t eres A) →
  envs_entails ℶ1 (refines E t e A).
Proof.
  rewrite envs_entails_unseal. intros ?????? Hg.
  subst e eres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite (refines_xchg_r E K) //.
  rewrite Hg.
  apply bi.wand_elim_l.
Qed.

Tactic Notation "rel_xchg_l" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ _)%I) => l end in
    iAssumptionCore || fail "rel_xchg_l: cannot find" l "↦ₛ ?" in
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_xchg_l_simpl K);
       [reflexivity (** e = fill K (#l <- e') *)
       |iSolveTC    (** e' is a value *)
       |idtac..])
    |fail 1 "rel_xchg_l: cannot find 'Xchg'"];
  (* the remaining goals are from tac_rel_xchg_l (except for the first one, which has already been solved by this point) *)
  [iSolveTC        (** IntoLaters *)
  |solve_mapsto ()
  |pm_reflexivity || fail "rel_xchg_l: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].

Tactic Notation "rel_xchg_l_atomic" := rel_apply_l refines_xchg_l.

Tactic Notation "rel_xchg_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ _)%I) => l end in
    iAssumptionCore || fail "rel_xchg_r: cannot find" l "↦ₛ ?" in
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_xchg_r K);
       [reflexivity|iSolveTC|idtac..])
    |fail 1 "rel_xchg_r: cannot find 'Xchg'"];
  (* the remaining goals are from tac_rel_xchg_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_xchg_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |pm_reflexivity || fail "rel_xchg_r: this should not happen O-:"
  |reflexivity
  |rel_finish  (** new goal *)].


(** Alloc *)
Tactic Notation "rel_alloc_l_atomic" := rel_apply_l refines_alloc_l.

Lemma tac_rel_alloc_l_simpl `{!relocG Σ} K ℶ1 ℶ2 e t e' v' A :
  e = fill K (Alloc e') →
  IntoVal e' v' →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  (envs_entails ℶ2 (∀ (l : loc),
     (l ↦ v' -∗ refines ⊤ (fill K (of_val #l)) t A))) →
  envs_entails ℶ1 (refines ⊤ e t A).
Proof.
  rewrite envs_entails_unseal. intros ???; subst.
  rewrite into_laterN_env_sound /=.
  rewrite -(refines_alloc_l _ ⊤); eauto.
  rewrite -fupd_intro.
  apply bi.later_mono.
Qed.

Tactic Notation "rel_alloc_l" ident(l) "as" constr(H) :=
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_alloc_l_simpl K);
       [reflexivity (** e = fill K (Alloc e') *)
       |iSolveTC    (** e' is a value *)
       |idtac..])
    |fail 1 "rel_alloc_l: cannot find 'Alloc'"];
  [iSolveTC        (** IntoLaters *)
  |iIntros (l) H; rel_finish  (** new goal *)].

Lemma tac_rel_alloc_r `{!relocG Σ} K' ℶ E t' v' e t A :
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
  rel_pures_r;
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

(** CmpXchg *)
(* TODO: non-atomic tactics for CmpXchg? *)
Tactic Notation "rel_cmpxchg_l_atomic" := rel_apply_l refines_cmpxchg_l.

Lemma tac_rel_cmpxchg_fail_r `{!relocG Σ} K ℶ1 i1 E (l : loc) e1 e2 v1 v2 v e t eres A :
  e = fill K (CmpXchg (# l) e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ v)%I →
  v ≠ v1 →
  vals_compare_safe v v1 →
  eres = fill K (v, #false)%V →
  envs_entails ℶ1 (refines E t eres A) →
  envs_entails ℶ1 (refines E t e A).
Proof.
  rewrite envs_entails_unseal. intros ???????? Hg.
  subst e eres.
  rewrite envs_lookup_split // /= Hg; simpl.
  apply bi.wand_elim_l'.
  eapply refines_cmpxchg_fail_r; eauto.
Qed.

Lemma tac_rel_cmpxchg_suc_r `{!relocG Σ} K ℶ1 ℶ2 i1 E (l : loc) e1 e2 v1 v2 v e t eres A :
  e = fill K (CmpXchg (# l) e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  nclose specN ⊆ E →
  envs_lookup i1 ℶ1 = Some (false, l ↦ₛ v)%I →
  v = v1 →
  vals_compare_safe v v1 →
  envs_simple_replace i1 false (Esnoc Enil i1 (l ↦ₛ v2)) ℶ1 = Some ℶ2 →
  eres = fill K (v, #true)%V →
  envs_entails ℶ2 (refines E t eres A) →
  envs_entails ℶ1 (refines E t e A).
Proof.
  rewrite envs_entails_unseal. intros ????????? Hg.
  subst e eres.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id Hg.
  apply bi.wand_elim_l'.
  eapply refines_cmpxchg_suc_r; eauto.
Qed.

Tactic Notation "rel_cmpxchg_fail_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ _)%I) => l end in
    iAssumptionCore || fail "rel_cmpxchg_fail_r: cannot find" l "↦ₛ ?" in
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_cmpxchg_fail_r K);
       [reflexivity  (** e = fill K (CmpXchg #l e1 e2) *)
       |iSolveTC     (** e1 is a value *)
       |iSolveTC     (** e2 is a value *)
       |idtac..])
    |fail 1 "rel_cmpxchg_fail_r: cannot find 'CmpXchg'"];
  (* the remaining goals are from tac_rel_cmpxchg_fail_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_cmpxchg_fail_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |try (simpl; congruence)   (** v ≠ v1 *)
  |try heap_lang.proofmode.solve_vals_compare_safe
  |reflexivity
  |rel_finish  (** new goal *)].

Tactic Notation "rel_cmpxchg_suc_r" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦ₛ _)%I) => l end in
    iAssumptionCore || fail "rel_cmpxchg_suc_r: cannot find" l "↦ₛ ?" in
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_cmpxchg_suc_r K);
       [reflexivity  (** e = fill K (CmpXchg #l e1 e2) *)
       |iSolveTC     (** e1 is a value *)
       |iSolveTC     (** e2 is a value *)
       |idtac..])
    |fail 1 "rel_cmpxchg_suc_r: cannot find 'CmpXchg'"];
  (* the remaining goals are from tac_rel_cmpxchg_suc_r (except for the first one, which has already been solved by this point) *)
  [solve_ndisj || fail "rel_cmpxchg_suc_r: cannot prove 'nclose specN ⊆ ?'"
  |solve_mapsto ()
  |try (simpl; congruence)   (** v = v1 *)
  |try heap_lang.proofmode.solve_vals_compare_safe
  |pm_reflexivity  (** new env *)
  |reflexivity
  |rel_finish  (** new goal *)].

(** NewProph *)
Tactic Notation "rel_newproph_l_atomic" := rel_apply_l refines_newproph_l.

Lemma tac_rel_newproph_l_simpl `{!relocG Σ} K ℶ1 ℶ2 e t A :
  e = fill K NewProph →
  MaybeIntoLaterNEnvs 1 ℶ1 ℶ2 →
  (envs_entails ℶ2 (∀ (vs : list (val*val)) (p : proph_id),
     (proph p vs -∗ refines ⊤ (fill K (of_val #p)) t A))) →
  envs_entails ℶ1 (refines ⊤ e t A).
Proof.
  rewrite envs_entails_unseal. intros ???; subst.
  rewrite into_laterN_env_sound /=.
  rewrite -(refines_newproph_l _ ⊤); eauto.
  rewrite -fupd_intro.
  by apply bi.later_mono.
Qed.

Tactic Notation "rel_newproph_l" ident(p) ident(vs) "as" constr(H) :=
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_newproph_l_simpl K);
       [reflexivity (** e = fill K (NewProph e') *)
       |idtac..])
    |fail 1 "rel_newproph_l: cannot find 'NewProph'"];
  [iSolveTC                      (** IntoLaters *)
  |iIntros (p vs) H; rel_finish  (** new goal *)].

Lemma tac_rel_newproph_r `{!relocG Σ} K' ℶ E e t A :
  t = fill K' NewProph →
  nclose specN ⊆ E →
  envs_entails ℶ (∀ (p : proph_id), refines E e (fill K' #p) A) →
  envs_entails ℶ (refines E e t A).
Proof.
  intros ???. subst t.
  rewrite -refines_newproph_r //.
Qed.

Tactic Notation "rel_newproph_r" ident(p) :=
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_newproph_r K);
       [reflexivity  (** t = K'[newproph] *)
       |idtac..])
    |fail 1 "rel_newproph_r: cannot find 'NewProph'"];
  [solve_ndisj || fail "rel_newproph_r: cannot prove 'nclose specN ⊆ ?'"
  |iIntros (p); rel_finish  (** new goal *)].

Tactic Notation "rel_newproph_r" :=
  let p := fresh in
  rel_newproph_r p.

Tactic Notation "rel_newproph_l" :=
  let p := fresh in
  let vs := fresh in
  let H := iFresh "H" in
  rel_newproph_l p vs as H.

(** ResolveProph *)
(* TODO: implement this lol *)
Lemma tac_rel_resolveproph_r `{!relocG Σ} K' ℶ E (p :proph_id) w e t A :
  t = fill K' (ResolveProph #p (of_val w)) →
  nclose specN ⊆ E →
  envs_entails ℶ (refines E e (fill K' #()) A) →
  envs_entails ℶ (refines E e t A).
Proof.
  intros ???. subst t.
  rewrite -refines_resolveproph_r //.
Qed.

Tactic Notation "rel_resolveproph_r" :=
  rel_pures_r;
  first
    [rel_reshape_cont_r ltac:(fun K e' =>
       eapply (tac_rel_resolveproph_r K);
       [reflexivity  (** t = K'[resolveproph] *)
       |idtac..])
    |fail 1 "rel_resolveproph_r: cannot find 'ResolveProph'"];
  [solve_ndisj || fail "rel_resolveproph_r: cannot prove 'nclose specN ⊆ ?'"
  |rel_finish  (** new goal *)].


(** Fork *)
Lemma tac_rel_fork_l `{!relocG Σ} K ℶ E e' eres e t A :
  e = fill K (Fork e') →
  is_closed_expr ∅ e' →
  eres = fill K #() →
  envs_entails ℶ (|={⊤,E}=> ▷ (WP e' {{ _ , True%I }} ∗ refines E eres t A))%I →
  envs_entails ℶ (refines ⊤ e t A).
Proof.
  intros ????. subst e eres.
  rewrite -refines_fork_l //.
Qed.

Tactic Notation "rel_fork_l" :=
  rel_pures_l;
  first
    [rel_reshape_cont_l ltac:(fun K e' =>
       eapply (tac_rel_fork_l K); first reflexivity)
    |fail 1 "rel_fork_l: cannot find 'Fork'"];
  (* the remaining goals are from tac_rel_load_r (except for the first one, which has already been solved by this point) *)
  [try fast_done    (** is_closed_expr [] e' *)
  |reflexivity    || fail "rel_fork_l: this should not happen O-:"
  |rel_finish  (** new goal *)].

Lemma tac_rel_fork_r `{!relocG Σ} K ℶ E e' e t eres A :
  e = fill K (Fork e') →
  nclose specN ⊆ E →
  is_closed_expr ∅ e' →
  eres = fill K #() →
  envs_entails ℶ (∀ k, refines_right k e' -∗ refines E t eres A) →
  envs_entails ℶ (refines E t e A).
Proof.
  intros ?????. subst e eres.
  by rewrite -refines_fork_r //.
Qed.

Tactic Notation "rel_fork_r" ident(i) "as" constr(H) :=
  rel_pures_r;
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
  assert (H := AsRecV_recv);
  rel_pure_l (App _ _);
  clear H.
Tactic Notation "rel_rec_r" :=
  let H := fresh in
  assert (H := AsRecV_recv);
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

Ltac rel_arrow_val :=
  rel_pures_l; rel_pures_r;
  (iApply refines_arrow_val
  || fail "rel_arrow_val: cannot apply the closure rule");
  iModIntro.

Ltac rel_arrow :=
  rel_pures_l; rel_pures_r;
  (iApply refines_arrow
  || fail "rel_arrow: cannot apply the closure rule");
  iModIntro.
