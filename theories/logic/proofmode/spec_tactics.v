(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Tactics for updating the specification program. *)
From iris.proofmode Require Import
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction.
From reloc.logic Require Export model spec_rules.
Set Default Proof Using "Type".

(** * TP tactics *)

(** ** bind *)
Lemma tac_tp_bind_gen `{relocG Σ} k Δ Δ' i p e e' Q :
  envs_lookup i Δ = Some (p, refines_right k e)%I →
  e = e' →
  envs_simple_replace i p (Esnoc Enil i (refines_right k e')) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof.
  rewrite envs_entails_unseal. intros; subst. simpl.
  rewrite envs_simple_replace_sound // /=.
  destruct p; rewrite /= ?right_id; by rewrite bi.wand_elim_r.
Qed.

Lemma tac_tp_bind `{relocG Σ} k e' Δ Δ' i p K' e Q :
  envs_lookup i Δ = Some (p, refines_right k e)%I →
  e = fill K' e' →
  envs_simple_replace i p (Esnoc Enil i (refines_right k (fill K' e'))) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof. intros. by eapply tac_tp_bind_gen. Qed.

Ltac tp_bind_helper :=
  simpl;
  lazymatch goal with
  | |- fill ?K ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.

Tactic Notation "tp_normalise" constr(j) :=
  iStartProof;
  eapply (tac_tp_bind_gen j);
    [iAssumptionCore (* prove the lookup *)
    | lazymatch goal with
      | |- fill ?K ?e = _ =>
          by rewrite /= ?fill_app /=
      | |- ?e = _ => try fast_done
      end
    |reflexivity
    |(* new goal *)].

Tactic Notation "tp_bind" constr(j) open_constr(efoc) :=
  iStartProof;
  eapply (tac_tp_bind j efoc);
    [iAssumptionCore (* prove the lookup *)
    |tp_bind_helper (* do actual work *)
    |reflexivity
    |(* new goal *)].

Lemma tac_tp_pure `{relocG Σ} e K' e1 k e2 Δ1 E1 i1 e' ϕ ψ Q n :
  (* we have those premises first, because we will be trying to solve them
     with backtracking using reashape_expr; see the accompanying Ltac.
     the first premise decomposes the expression, the second one checks
     that we can make a pure step *)
  e = fill K' e1 →
  PureExec ϕ n e1 e2 →
  (∀ P, ElimModal ψ false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, refines_right k e)%I →
  ψ →
  ϕ →
  (* we will call simpl on this goal thus re-composing the expression again *)
  e' = fill K' e2 →
  match envs_simple_replace i1 false (Esnoc Enil i1 (refines_right k e')) Δ1 with
  | Some Δ2 => envs_entails Δ2 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros -> Hpure ?? HΔ1 Hψ Hϕ -> ?.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; try done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite /refines_right.
  rewrite -!fill_app.
  rewrite step_pure //.
  rewrite -[Q]elim_modal // /=.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_pure" constr(j) open_constr(ef) :=
  iStartProof;
  lazymatch goal with
  | |- context[environments.Esnoc _ ?H (refines_right j (fill ?K' ?e))] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure (fill K' e) (K++K') e' j);
      [by rewrite ?fill_app | tc_solve | ..])
  | |- context[environments.Esnoc _ ?H (refines_right j ?e)] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_tp_pure e K e' j);
      [by rewrite ?fill_app | tc_solve | ..])
  end;
  [tc_solve || fail "tp_pure: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_pure: cannot prove 'nclose specN ⊆ ?'"
  (* |iAssumptionCore || fail "tp_pure: cannot find spec_ctx" (* spec_ctx *) *)
  |iAssumptionCore || fail "tp_pure: cannot find the RHS" (* TODO fix error message *)
  |try (exact I || reflexivity) (* ψ *)
  |try (exact I || reflexivity) (* ϕ *)
  |simpl; reflexivity ||  fail "tp_pure: this should not happen" (* e' = fill K' e2 *)
  |pm_reduce (* new goal *)].


Tactic Notation "tp_pures" constr (j) := repeat (tp_pure j _).
Tactic Notation "tp_rec" constr(j) :=
  let H := fresh in
  assert (H := AsRecV_recv);
  tp_pure j (App _ _);
  clear H.
Tactic Notation "tp_seq" constr(j) := tp_rec j.
Tactic Notation "tp_let" constr(j) := tp_rec j.
Tactic Notation "tp_lam" constr(j) := tp_rec j.
Tactic Notation "tp_fst" constr(j) := tp_pure j (Fst (PairV _ _)).
Tactic Notation "tp_snd" constr(j) := tp_pure j (Snd (PairV _ _)).
Tactic Notation "tp_proj" constr(j) := tp_pure j (_ (PairV _ _)).
Tactic Notation "tp_case_inl" constr(j) := tp_pure j (Case (InjLV _) _ _).
Tactic Notation "tp_case_inr" constr(j) := tp_pure j (Case (InjRV _) _ _).
Tactic Notation "tp_case" constr(j) := tp_pure j (Case _ _ _).
Tactic Notation "tp_binop" constr(j) := tp_pure j (BinOp _ _ _).
Tactic Notation "tp_op" constr(j) := tp_binop j.
Tactic Notation "tp_if_true" constr(j) := tp_pure j (If #true _ _).
Tactic Notation "tp_if_false" constr(j) := tp_pure j (If #false _ _).
Tactic Notation "tp_if" constr(j) := tp_pure j (If _ _ _).
Tactic Notation "tp_pair" constr(j) := tp_pure j (Pair _ _).
Tactic Notation "tp_closure" constr(j) := tp_pure j (Rec _ _ _).

Lemma tac_tp_store `{relocG Σ} k Δ1 Δ2 E1 i1 i2 K' e (l : loc) e' e2 v' v Q :
  (* TODO: here instead of True we can consider another Coq premise, like in tp_pure.
     Same goes for the rest of those tactics *)
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, refines_right k e, Δ2)%I →
  e = fill K' (Store (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  e2 = fill K' #() →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ v')%I →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (refines_right k e2)) i2 (l ↦ₛ v)) Δ2 with
  | None => False
  | Some Δ3 => envs_entails Δ3 Q
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite /IntoVal.
  rewrite envs_entails_unseal. intros ??? -> <- -> ? HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite !assoc -(assoc _ spec_ctx).
  rewrite -fill_app step_store // fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ v)%I). simpl.
  rewrite assoc. rewrite (comm _ spec_ctx (l ↦ₛ _)%I).
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_store" constr(j) :=
  iStartProof;
  eapply (tac_tp_store j);
  [tc_solve || fail "tp_store: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_store: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_store: cannot find '" j " ' RHS"
  |tp_bind_helper
  |tc_solve || fail "tp_store: cannot convert the argument to a value"
  |simpl; reflexivity || fail "tp_store: this should not happen"
  |iAssumptionCore || fail "tp_store: cannot find '? ↦ₛ ?'"
  |pm_reduce (* new goal *)].


Lemma tac_tp_xchg `{relocG Σ} k Δ1 Δ2 E1 i1 i2 K' e (l : loc) e' e2 v' v Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, refines_right k e, Δ2)%I →
  e = fill K' (Xchg (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ v')%I →
  e2 = fill K' (of_val v') →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (refines_right k e2)) i2 (l ↦ₛ v)) Δ2 with
  | None => False
  | Some Δ3 => envs_entails Δ3 Q
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite /IntoVal.
  rewrite envs_entails_unseal. intros ??? -> <- ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite !assoc -(assoc _ spec_ctx).
  rewrite -fill_app step_xchg // fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ v)%I). simpl.
  rewrite assoc. rewrite (comm _ spec_ctx (l ↦ₛ _)%I).
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_xchg" constr(j) :=
  iStartProof;
  eapply (tac_tp_store j);
  [tc_solve || fail "tp_store: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_store: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_store: cannot find '" j " ' RHS"
  |tp_bind_helper
  |tc_solve || fail "tp_store: cannot convert the argument to a value"
  |iAssumptionCore || fail "tp_store: cannot find '? ↦ₛ ?'"
  |simpl; reflexivity || fail "tp_store: this should not happen"
  |pm_reduce (* new goal *)].

(* *)
(* DF: *)
(* If [envs_lookup i1 Δ1 = Some (p, spec_ctx ρ)] and *)
(*    [envs_lookup i2 Δ1 = Some (false, j ⤇ fill K e)], *)
(* how can we prove that [i1 <> i2]? If we can do that then we can utilize *)
(* the lemma [envs_lookup_envs_delete_ne]. *)
(* *)

Lemma tac_tp_load `{relocG Σ} k Δ1 Δ2 E1 i1 i2 K' e e2 (l : loc) v Q q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, refines_right k e, Δ2)%I →
  e = fill K' (Load #l) →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ{q} v)%I →
  e2 = fill K' (of_val v) →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (refines_right k e2)) i2 (l ↦ₛ{q} v)%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite /refines_right.
  rewrite right_id.
  rewrite assoc. rewrite -(assoc _ spec_ctx).
  rewrite -fill_app step_load /= // fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ{q} v)%I).
  rewrite assoc.
  rewrite (comm _ _ (l ↦ₛ{q} v)%I).
  rewrite -assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_load" constr(j) :=
  iStartProof;
  eapply (tac_tp_load j);
  [tc_solve || fail "tp_load: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_load: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_load: cannot find the RHS '" j "'"
  |tp_bind_helper
  |iAssumptionCore || fail "tp_load: cannot find '? ↦ₛ ?'"
  |simpl; reflexivity || fail "tp_load: this should not happen"
  |pm_reduce (* new goal *)].

Lemma tac_tp_cmpxchg_fail `{relocG Σ} k Δ1 Δ2 E1 i1 i2 K' e enew (l : loc) e1 e2 v' v1 v2 Q q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, refines_right k e, Δ2)%I →
  e = fill K' (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ{q} v')%I →
  v' ≠ v1 →
  vals_compare_safe v' v1 →
  enew = fill K' (v', #false)%V →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (refines_right k enew)) i2 (l ↦ₛ{q} v')%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    =>  False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> Hv1 Hv2 ??? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite /refines_right. rewrite -fill_app.
  rewrite assoc. rewrite -(assoc _ spec_ctx).
  rewrite step_cmpxchg_fail //. rewrite fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ{q} _)%I).
  rewrite assoc.
  rewrite (comm _ _ (l ↦ₛ{q} _)%I).
  rewrite -assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_cmpxchg_fail" constr(j) :=
  iStartProof;
  eapply (tac_tp_cmpxchg_fail j);
    [tc_solve || fail "tp_cmpxchg_fail: cannot eliminate modality in the goal"
    |solve_ndisj || fail "tp_cmpxchg_fail: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_cmpxchg_fail: cannot find the RHS '" j "'"
    |tp_bind_helper (* e = K'[CmpXchg _ _ _] *)
    |tc_solve || fail "tp_cmpxchg_fail: argument is not a value"
    |tc_solve || fail "tp_cmpxchg_fail: argument is not a value"
    |iAssumptionCore || fail "tp_cmpxchg_fail: cannot find '? ↦ ?'"
    |try (simpl; congruence) (* v' ≠ v1 *)
    |try heap_lang.proofmode.solve_vals_compare_safe
    |simpl; reflexivity || fail "tp_cmpxchg_fail: this should not happen"
    |pm_reduce (* new goal *)].

Lemma tac_tp_cmpxchg_suc `{relocG Σ} k Δ1 Δ2 E1 i1 i2 K' e enew (l : loc) e1 e2 v' v1 v2 Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, refines_right k e, Δ2)%I →
  e = fill K' (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ v')%I →
  v' = v1 →
  vals_compare_safe v' v1 →
  enew = fill K' (v', #true)%V →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (refines_right k enew)) i2 (l ↦ₛ v2)%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> Hv1 Hv2 ??? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite /refines_right. rewrite -fill_app.
  rewrite assoc. rewrite -(assoc _ spec_ctx).
  rewrite step_cmpxchg_suc //. rewrite fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ _)%I) assoc.
  rewrite (comm _ _ (l ↦ₛ _)%I) -assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_cmpxchg_suc" constr(j) :=
  iStartProof;
  eapply (tac_tp_cmpxchg_suc j);
  [tc_solve || fail "tp_cmpxchg_suc: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_cmpxchg_suc: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_cmpxchg_suc: cannot the RHS '" j "'"
  |tp_bind_helper (* e = K'[CmpXchg _ _ _] *)
  |tc_solve || fail "tp_cmpxchg_suc: argument is not a value"
  |tc_solve || fail "tp_cmpxchg_suc: argument is not a value"
  |iAssumptionCore || fail "tp_cmpxchg_suc: cannot find '? ↦ ?'"
  |try (simpl; congruence)     (* v' = v1 *)
  |try heap_lang.proofmode.solve_vals_compare_safe
  |simpl; reflexivity || fail "tp_cmpxchg_suc: this should not happen"
  |pm_reduce (* new goal *)].

Lemma tac_tp_faa `{relocG Σ} k Δ1 Δ2 E1 i1 i2 K' e enew (l : loc)  e2 (z1 z2 : Z) Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup_delete false i1 Δ1 = Some (false, refines_right k e, Δ2)%I →
  e = fill K' (FAA #l e2) →
  IntoVal e2 #z2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ₛ #z1)%I →
  enew = fill K' #z1 →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (refines_right k enew)) i2 (l ↦ₛ #(z1+z2))%I) Δ2 with
    | Some Δ3 =>   envs_entails Δ3 Q
    | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> ?? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite /refines_right. rewrite -fill_app.
  rewrite assoc. rewrite -(assoc _ spec_ctx).
  rewrite step_faa //. rewrite fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ _)%I) assoc.
  rewrite (comm _ _ (l ↦ₛ _)%I) -assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "tp_faa" constr(j) :=
  iStartProof;
  eapply (tac_tp_faa j);
  [tc_solve || fail "tp_faa: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_faa: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_faa: cannot find the RHS '" j "'"
  |tp_bind_helper (* e = K'[FAA _ _ _] *)
  |tc_solve (* IntoVal *)
  |iAssumptionCore || fail "tp_faa: cannot find '? ↦ ?'"
  |simpl;reflexivity || fail "tp_faa: this should not happen"
  |pm_reduce (* new goal *)].


Lemma tac_tp_fork `{relocG Σ} k Δ1 E1 i1 K' e enew e' Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, refines_right k e)%I →
  e = fill K' (Fork e') →
  enew = fill K' #() →
  match envs_simple_replace i1 false
      (Esnoc Enil i1 (refines_right k (fill K' #()))) Δ1 with
  | Some Δ2 => envs_entails Δ2 (∀ k', refines_right k' e' -∗ Q)%I
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ???->-> HQ.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; last done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite /refines_right. rewrite -fill_app.
  rewrite step_fork //. rewrite fill_app.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim. intros j'.
  (* rewrite (comm _ (j ⤇ _)%I (j' ⤇ _)%I). *)
  rewrite (comm _ _ (spec_ctx ∗ j' ⤇ e')%I).
  rewrite -assoc.
  rewrite bi.wand_elim_r.
  rewrite HQ. rewrite /refines_right.
  rewrite (bi.forall_elim (RefId j' [])) /=.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_fork" constr(j) :=
  iStartProof;
  eapply (tac_tp_fork j);
  [tc_solve || fail "tp_fork: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_fork: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_fork: cannot find the RHS '" j "'"
  |tp_bind_helper
  |simpl; reflexivity || fail "tp_fork: this should not happen"
  |pm_reduce (* new goal *)].

Tactic Notation "tp_fork" constr(j) "as" ident(j') constr(H) :=
  iStartProof;
  eapply (tac_tp_fork j);
  [tc_solve || fail "tp_fork: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_fork: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_fork: cannot find the RHS '" j "'"
  |tp_bind_helper
  |simpl; reflexivity || fail "tp_fork: this should not happen"
  |pm_reduce;
   (iIntros (j') || fail 1 "tp_fork: " j' " not fresh ");
   (iIntros H || fail 1 "tp_fork: " H " not fresh")
(* new goal *)].

Tactic Notation "tp_fork" constr(j) "as" ident(j') :=
  let H := iFresh in tp_fork j as j' H.

Lemma tac_tp_alloc `{relocG Σ} k Δ1 E1 i1 K' e e' v Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, refines_right k e)%I →
  e = fill K' (ref e') →
  IntoVal e' v →
  (* TODO use match here as well *)
  (∀ l : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (refines_right k (fill K' #l))) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((l ↦ₛ v) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? Hfill <- HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite /refines_right.
  rewrite Hfill -fill_app /=.
  rewrite step_alloc //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r, bi.wand_intro_l.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim=> l.
  destruct (HQ l) as (Δ2 & HΔ2 & HQ').
  rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
  rewrite HQ' right_id.
  rewrite /refines_right fill_app.
  rewrite (comm _ _ (l ↦ₛ _)%I).
  rewrite assoc.
  rewrite (comm _ _ (l ↦ₛ _)%I).
  rewrite -(assoc _ (l ↦ₛ _)%I spec_ctx _). rewrite -assoc.
  rewrite bi.wand_elim_r.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_alloc" constr(j) "as" ident(l) constr(H) :=
  let finish _ :=
      first [ intros l | fail 1 "tp_alloc:" l "not fresh"];
        eexists; split;
        [ reduction.pm_reflexivity
        | (iIntros H; tp_normalise j) || fail 1 "tp_alloc:" H "not correct intro pattern" ] in
  iStartProof;
  eapply (tac_tp_alloc j);
  [tc_solve || fail "tp_alloc: cannot eliminate modality in the goal"
  |solve_ndisj || fail "tp_alloc: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "tp_alloc: cannot find the RHS '" j "'"
  |tp_bind_helper
  |tc_solve || fail "tp_alloc: expressions is not a value"
  |finish ()
(* new goal *)].

Tactic Notation "tp_alloc" constr(j) "as" ident(j') :=
  let H := iFresh in tp_alloc j as j' H.


(* *)
(* (**************************) *)
(* (* tp_apply *) *)

(* Fixpoint print_sel (ss : list sel_pat) (s : string) := *)
(*   match ss with *)
(*   | nil => s *)
(*   | SelPure :: ss' => (String "%" (String " " (print_sel ss' s))) *)
(*   | SelPersistent :: ss' =>  (String "#" (print_sel ss' s)) *)
(*   | SelSpatial :: ss' => (* no clue :( *) (print_sel ss' s) *)
(*   | SelIdent (INamed n) :: ss' => append n (String " " (print_sel ss' s)) *)
(*   | SelIdent (IAnon _) :: ss' => String "?" (String " " (print_sel ss' s)) *)
(*   (* wat to do with the index? *) *)
(*   end. *)

(* Ltac print_sel ss := *)
(*   lazymatch type of ss with *)
(*   | list sel_pat => eval vm_compute in (print_sel ss "") *)
(*   | string => ss *)
(*   end. *)

(* Definition appP (ss : option (list sel_pat)) (Hj Hs : string) := *)
(*   match ss with *)
(*   | Some ss' => cons (SelIdent Hs) (app ss' [SelIdent Hj]) *)
(*   | None => cons (SelIdent Hs) [SelIdent Hj] *)
(*   end. *)

(* Definition add_elim_pat (pat : string) (Hj : string) := *)
(*   match pat with *)
(*   | EmptyString => Hj *)
(*   | _ => append (String "[" (append Hj (String " " pat))) "]" *)
(*   end. *)

(* Tactic Notation "tp_apply" constr(j) open_constr(lem) "with" constr(Hs) "as" constr(Hr) := *)
(*   iStartProof; *)
(*   let rec find Γ j := *)
(*     match Γ with *)
(*     | Esnoc ?Γ (IAnon _) ?P => *)
(*       find Γ j *)
(*     | Esnoc ?Γ (INamed ?Hj) ?P => *)
(*       lazymatch P with *)
(*       | (j ⤇ _)%I => Hj *)
(*       | _ => find Γ j *)
(*       end *)
(*     | Enil => fail 2 "tp_apply: cannot find " j " ⤇ _ " *)
(*     | _ => fail 2 "tp_apply: unknown error in find" *)
(*     end in *)
(*   let rec findSpec Γp Γs := *)
(*     match Γp with *)
(*     | Esnoc ?Γ (IAnon _) _ => findSpec Γ Γs *)
(*     | Esnoc ?Γ (INamed ?Hspec) ?P => *)
(*       lazymatch P with *)
(*       | (spec_ctx _)%I => Hspec *)
(*       | _ => findSpec Γ Γs *)
(*       end *)
(*     | Enil => *)
(*       match Γs with *)
(*       | Enil => fail 2 "tp_apply: cannot find spec_ctx _" *)
(*       | _ => findSpec Γs Enil *)
(*       end *)
(*     | _ => fail 2 "tp_apply: unknown error in findSpec" *)
(*     end in *)
(*   match goal with *)
(*   | |- envs_entails (Envs ?Γp ?Γs) ?Q => *)
(*     let Hj := (find Γs j) in *)
(*     let Hspec := findSpec Γp Γs in *)
(*     let pat := eval vm_compute in (appP (sel_pat.parse Hs) Hj Hspec) in *)
(*     let pats := print_sel pat in *)
(*     let elim_pats := eval vm_compute in (add_elim_pat Hr Hj) in *)
(*     iMod (lem with pats) as elim_pats; first try by solve_ndisj *)
(*   | _ => fail "tp_apply: cannot parse the context" *)
(*   end. *)

(* Tactic Notation "tp_apply" constr(j) open_constr(lem) "with" constr(Hs) := tp_apply j lem with Hs as "". *)

(* Tactic Notation "tp_apply" constr(j) open_constr(lem) "as" constr(Hr) := tp_apply j lem with "" as Hr. *)

(* Tactic Notation "tp_apply" constr(j) open_constr(lem) := tp_apply j lem with "" as "". *)
(* *)
