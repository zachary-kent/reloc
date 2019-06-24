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
Lemma tac_tp_bind_gen `{relocG Σ} j Δ Δ' i p e e' Q :
  envs_lookup i Δ = Some (p, j ⤇ e)%I →
  e = e' →
  envs_simple_replace i p (Esnoc Enil i (j ⤇ e')) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof.
  rewrite envs_entails_eq. intros; subst. simpl.
  rewrite envs_simple_replace_sound // /=.
  destruct p; rewrite /= ?right_id; by rewrite bi.wand_elim_r.
Qed.

Lemma tac_tp_bind `{relocG Σ} j e' Δ Δ' i p K' e Q :
  envs_lookup i Δ = Some (p, j ⤇ e)%I →
  e = fill K' e' →
  envs_simple_replace i p (Esnoc Enil i (j ⤇ fill K' e')) Δ = Some Δ' →
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

Lemma tac_tp_pure `{relocG Σ} j K' e1 e2 Δ1 Δ2 E1 ρ i1 i2 p e ϕ ψ Q n :
  (∀ P, ElimModal ψ false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (p, spec_ctx ρ) →
  envs_lookup i2 Δ1 = Some (false, j ⤇ e)%I →
  e = fill K' e1 →
  PureExec ϕ n e1 e2 →
  ψ →
  ϕ →
  envs_simple_replace i2 false
    (Esnoc Enil i2
     (j ⤇ fill K' e2)) Δ1 = Some Δ2 →
  envs_entails Δ2 Q →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_eq. intros ?? HΔ1 ? Hfill Hpure Hψ Hϕ ??.
  rewrite -(idemp bi_and (of_envs Δ1)).
  rewrite {1}(envs_lookup_sound' Δ1 false). 2: apply HΔ1.
  rewrite bi.sep_elim_l.
  enough (<pers> spec_ctx ρ ∧ of_envs Δ1 -∗ Q) as <-.
  { rewrite -bi.intuitionistically_into_persistently_1.
    destruct p; simpl;
    by rewrite ?(bi.intuitionistic_intuitionistically (spec_ctx ρ)). }
  rewrite bi.persistently_and_intuitionistically_sep_l.
  rewrite bi.intuitionistic_intuitionistically.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i2) //; simpl.
  rewrite right_id Hfill.
  rewrite (assoc _ (spec_ctx ρ) (j ⤇ _)%I).
  rewrite step_pure //.
  rewrite -[Q]elim_modal // /=.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  by rewrite bi.wand_elim_r.
Qed.

Ltac with_spec_ctx tac :=
  lazymatch goal with
  | |- envs_entails _ (refines ?E ?e1 ?e2 ?A) =>
    let ρ := fresh in
    let H := iFresh in
    iApply (refines_spec_ctx E e1 e2 A);
    iDestruct 1 as (ρ) H;
    (tac (); iClear H; clear ρ)
  | _ => tac ()
  end.

(* TODO: The problem here is that it will fail if the redex is not specified, and is not on the top level *)
Tactic Notation "tp_pure" constr(j) open_constr(ef) :=
  iStartProof;
  with_spec_ctx ltac:(fun _ =>
  eapply (tac_tp_pure j _ ef);
    [iSolveTC || fail "tp_pure: cannot eliminate modality in the goal"
    |solve_ndisj || fail "tp_pure: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_pure: cannot find spec_ctx" (* spec_ctx *)
    |iAssumptionCore || fail "tp_pure: cannot find '" j " ⤇ ?'"
    |tp_bind_helper         (* e = K'[e1]*)
    |iSolveTC               (* PureExec ϕ n e1 e2 *)
    |try (exact I || reflexivity) (* ψ *)
    |try (exact I || reflexivity) (* ϕ *)
    |pm_reflexivity || fail "tp_pure: this should not happen"
    |(* new goal *)]).

Tactic Notation "tp_rec" constr(j) := tp_pure j (App _ _).
Tactic Notation "tp_seq" constr(j) := tp_rec j.
Tactic Notation "tp_let" constr(j) := tp_rec j.
Tactic Notation "tp_lam" constr(j) := tp_rec j.
Tactic Notation "tp_fst" constr(j) := tp_pure j (Fst (Pair _ _)).
Tactic Notation "tp_snd" constr(j) := tp_pure j (Snd (Pair _ _)).
Tactic Notation "tp_proj" constr(j) := tp_pure j (_ (Pair _ _)).
Tactic Notation "tp_case_inl" constr(j) := tp_pure j (Case (InjL _) _ _).
Tactic Notation "tp_case_inr" constr(j) := tp_pure j (Case (InjR _) _ _).
Tactic Notation "tp_case" constr(j) := tp_pure j (Case _ _ _).
Tactic Notation "tp_binop" constr(j) := tp_pure j (BinOp _ _ _).
Tactic Notation "tp_op" constr(j) := tp_binop j.
Tactic Notation "tp_if_true" constr(j) := tp_pure j (If #true _ _).
Tactic Notation "tp_if_false" constr(j) := tp_pure j (If #false _ _).
Tactic Notation "tp_if" constr(j) := tp_pure j (If _ _ _).
Tactic Notation "tp_pair" constr(j) := tp_pure j (Pair _ _).
Tactic Notation "tp_closure" constr(j) := tp_pure j (Rec _ _ _).

Lemma tac_tp_store `{relocG Σ} j Δ1 Δ2 Δ3 E1 ρ i1 i2 i3 p K' e (l : loc) e' v' v Q :
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  (* TODO: ^ boolean values here *)
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (p, spec_ctx ρ) →
  envs_lookup_delete false i2 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K' (Store (# l) e') →
  envs_lookup i3 Δ2 = Some (false, l ↦ₛ v')%I →
  IntoVal e' v →
  envs_simple_replace i3 false
     (Esnoc (Esnoc Enil i2 (j ⤇ fill K' #())) i3 (l ↦ₛ v)) Δ2 = Some Δ3 →
  (envs_entails Δ3 Q) →
  (envs_entails Δ1 Q).
Proof.
  rewrite envs_entails_eq. intros ???? Hfill ?<-? HQ.
  rewrite -(idemp bi_and (of_envs Δ1)).
  rewrite {1}(envs_lookup_sound' _ false). 2: eassumption.
  rewrite bi.sep_elim_l.
  enough (spec_ctx ρ ∗ of_envs Δ1 -∗ Q) as Hq.
  { rewrite -Hq.
    destruct p; simpl; last rewrite -(bi.intuitionistic_intuitionistically (spec_ctx ρ));
    rewrite {1}bi.intuitionistically_into_persistently_1 bi.persistently_and_intuitionistically_sep_l;
    by rewrite (bi.intuitionistic_intuitionistically (spec_ctx ρ)). }
  rewrite envs_lookup_delete_sound //; simpl.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite !assoc -(assoc _ (spec_ctx _)) Hfill.
  rewrite step_store //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ₛ v)%I).
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_store" constr(j) :=
  iStartProof;
  with_spec_ctx ltac:(fun _ =>
  eapply (tac_tp_store j);
    [iSolveTC || fail "tp_store: cannot eliminate modality in the goal"
    |solve_ndisj || fail "tp_store: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_store: cannot find spec_ctx" (* spec_ctx *)
    |iAssumptionCore || fail "tp_store: cannot find '" j " ⤇ ?'"
    |tp_bind_helper
    |iAssumptionCore || fail "tp_store: cannot find '? ↦ₛ ?'"
    |iSolveTC || fail "tp_store: cannot convert the argument to a value"
    |pm_reflexivity || fail "tp_store: this should not happen"
    |(* new goal *)]).

(*
DF:
If [envs_lookup i1 Δ1 = Some (p, spec_ctx ρ)] and
   [envs_lookup i2 Δ1 = Some (false, j ⤇ fill K e)],
how can we prove that [i1 <> i2]? If we can do that then we can utilize
the lemma [envs_lookup_envs_delete_ne].
*)

Lemma tac_tp_load `{relocG Σ} j Δ1 Δ2 Δ3 E1 E2 ρ i1 i2 i3 p K' e (l : loc) v Q q :
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (p, spec_ctx ρ) →
  envs_lookup_delete false i2 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K' (Load #l) →
  envs_lookup i3 Δ2 = Some (false, l ↦ₛ{q} v)%I →
  envs_simple_replace i3 false
    (Esnoc (Esnoc Enil i2 (j ⤇ fill K' (of_val v))) i3 (l ↦ₛ{q} v)%I) Δ2 = Some Δ3 →
  (envs_entails Δ3 (|={E1,E2}=> Q)) →
  (envs_entails Δ1 (|={E1,E2}=> Q)).
Proof.
  rewrite envs_entails_eq. intros ??? Hfill ?? HQ.
  rewrite -(idemp bi_and (of_envs Δ1)).
  rewrite {1}(envs_lookup_sound' Δ1 false). 2: eassumption.
  rewrite bi.sep_elim_l.
  enough (<pers> spec_ctx ρ ∧ of_envs Δ1 ={E1,E2}=∗ Q) as <-.
  { rewrite -bi.intuitionistically_into_persistently_1.
    destruct p; simpl;
    by rewrite ?(bi.intuitionistic_intuitionistically (spec_ctx ρ)). }
  rewrite bi.persistently_and_intuitionistically_sep_l.
  rewrite bi.intuitionistic_intuitionistically.
  rewrite envs_lookup_delete_sound //; simpl.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i3) //; simpl.
  rewrite right_id Hfill.
  (* (S (spec_ctx ρ) (S (j => fill) (S (l ↦ v) ..))) *)
  rewrite (assoc _ (spec_ctx ρ) (j ⤇ fill K' (Load _))%I).
  (* (S (S (spec_ctx ρ) (j => fill)) (S (l ↦ v) ..)) *)
  rewrite assoc.
  rewrite -(assoc _ (spec_ctx ρ) (j ⤇ fill K' (Load _))%I).
  rewrite (step_load _ ρ j K' l q v) //.
  rewrite -(fupd_trans E1 E1 E2).
  rewrite fupd_frame_r.
  apply fupd_mono.
  by rewrite (comm _ (j ⤇ _)%I) bi.wand_elim_r.
Qed.

Tactic Notation "tp_load" constr(j) :=
  iStartProof;
  with_spec_ctx ltac:(fun _ =>
  eapply (tac_tp_load j);
    [solve_ndisj || fail "tp_load: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_load: cannot find spec_ctx" (* spec_ctx *)
    |iAssumptionCore || fail "tp_load: cannot find '" j " ⤇ ?'"
    |tp_bind_helper
    |iAssumptionCore || fail "tp_load: cannot find '? ↦ₛ ?'"
    |pm_reflexivity || fail "tp_load: this should not happen"
    |(* new goal *)]).

Lemma tac_tp_cmpxchg_fail `{relocG Σ} j Δ1 Δ2 Δ3 E1 E2 ρ i1 i2 i3 p K' e (l : loc) e1 e2 v' v1 v2 Q q :
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (p, spec_ctx ρ) →
  envs_lookup_delete false i2 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K' (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i3 Δ2 = Some (false, l ↦ₛ{q} v')%I →
  val_for_compare v' ≠ val_for_compare v1 →
  vals_cmpxchg_compare_safe v' v1 →
  envs_simple_replace i3 false
    (Esnoc (Esnoc Enil i2 (j ⤇ fill K' (v', #false)%V)) i3 (l ↦ₛ{q} v')%I) Δ2 = Some Δ3 →
  envs_entails Δ3 (|={E1,E2}=> Q) →
  envs_entails Δ1 (|={E1,E2}=> Q).
Proof.
  rewrite envs_entails_eq. intros ??? Hfill <-<-? Hcmpxchg ?? HQ.
  rewrite -(idemp bi_and (of_envs Δ1)).
  rewrite {1}(envs_lookup_sound' Δ1 false). 2: eassumption.
  rewrite bi.sep_elim_l.
  enough (<pers> spec_ctx ρ ∧ of_envs Δ1 ={E1,E2}=∗ Q) as <-.
  { rewrite -bi.intuitionistically_into_persistently_1.
    destruct p; simpl;
    by rewrite ?(bi.intuitionistic_intuitionistically (spec_ctx ρ)). }
  rewrite bi.persistently_and_intuitionistically_sep_l.
  rewrite bi.intuitionistic_intuitionistically.
  rewrite envs_lookup_delete_sound // /=.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i3) // /=.
  rewrite Hfill.
  (* (S (spec_ctx ρ) (S (j => fill _ _) (S (l ↦ v) ..))) *)
  rewrite (assoc _ (spec_ctx ρ) (j ⤇ fill K' _)%I).
  (* (S (S (spec_ctx ρ) (j => fill _ _)) (S (l ↦ v) ..)) *)
  rewrite assoc.
  rewrite -(assoc _ (spec_ctx ρ) (j ⤇ fill K' _)%I).
  rewrite step_cmpxchg_fail //.
  rewrite -(fupd_trans E1 E1 E2).
  rewrite fupd_frame_r.
  apply fupd_mono.
  by rewrite (comm _ (j ⤇ _)%I) /= right_id bi.wand_elim_r.
Qed.

Tactic Notation "tp_cmpxchg_fail" constr(j) :=
  iStartProof;
  with_spec_ctx ltac:(fun _ =>
  eapply (tac_tp_cmpxchg_fail j);
    [solve_ndisj || fail "tp_cmpxchg_fail: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_cmpxchg_fail: cannot find spec_ctx" (* spec_ctx *)
    |iAssumptionCore || fail "tp_cmpxchg_fail: cannot find '" j " ⤇ ?'"
    |tp_bind_helper (* e = K'[CmpXchg _ _ _] *)
    |iSolveTC
    |iSolveTC
    |iAssumptionCore || fail "tp_cmpxchg_fail: cannot find '? ↦ ?'"
    |try (simpl; congruence) (* v' ≠ v1 *)
    |try heap_lang.proofmode.solve_vals_cmpxchg_compare_safe
    |pm_reflexivity || fail "tp_cmpxchg_fail: this should not happen"
    |(* new goal *)]).

Lemma tac_tp_cmpxchg_suc `{relocG Σ} j Δ1 Δ2 Δ3 E1 E2 ρ i1 i2 i3 p K' e (l : loc) e1 e2 v' v1 v2 Q :
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (p, spec_ctx ρ) →
  envs_lookup_delete false i2 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K' (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i3 Δ2 = Some (false, l ↦ₛ v')%I →
  val_for_compare v' = val_for_compare v1 →
  vals_cmpxchg_compare_safe v' v1 →
  envs_simple_replace i3 false
    (Esnoc (Esnoc Enil i2 (j ⤇ fill K' (v', #true)%V)) i3 (l ↦ₛ v2)%I) Δ2 = Some Δ3 →
  envs_entails Δ3 (|={E1,E2}=> Q) →
  envs_entails Δ1 (|={E1,E2}=> Q).
Proof.
  rewrite envs_entails_eq. intros ??? Hfill <-<-? Hcmpxchg Hsafe ? HQ.
  rewrite -(idemp bi_and (of_envs Δ1)).
  rewrite {1}(envs_lookup_sound' Δ1 false). 2: eassumption.
  rewrite bi.sep_elim_l.
  enough (<pers> spec_ctx ρ ∧ of_envs Δ1 ={E1,E2}=∗ Q) as <-.
  { rewrite -bi.intuitionistically_into_persistently_1.
    destruct p; simpl;
    by rewrite ?(bi.intuitionistic_intuitionistically (spec_ctx ρ)). }
  rewrite bi.persistently_and_intuitionistically_sep_l.
  rewrite bi.intuitionistic_intuitionistically.
  rewrite envs_lookup_delete_sound // /=.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i3) //.
  simpl. rewrite right_id Hfill.
  (* (S (spec_ctx ρ) (S (j => fill _ _) (S (l ↦ v) ..))) *)
  rewrite (assoc _ (spec_ctx ρ) (j ⤇ fill K' _)%I).
  (* (S (S (spec_ctx ρ) (j => fill _ _)) (S (l ↦ v) ..)) *)
  rewrite assoc.
  rewrite -(assoc _ (spec_ctx ρ) (j ⤇ fill K' _)%I).
  rewrite step_cmpxchg_suc //.
  rewrite -(fupd_trans E1 E1 E2).
  rewrite fupd_frame_r.
  apply fupd_mono.
  by rewrite (comm _ (j ⤇ _)%I) bi.wand_elim_r.
Qed.

Tactic Notation "tp_cmpxchg_suc" constr(j) :=
  iStartProof;
  with_spec_ctx ltac:(fun _ =>
  eapply (tac_tp_cmpxchg_suc j);
    [solve_ndisj || fail "tp_cmpxchg_suc: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_cmpxchg_suc: cannot find spec_ctx" (* spec_ctx *)
    |iAssumptionCore || fail "tp_cmpxchg_suc: cannot find '" j " ⤇ ?'"
    |tp_bind_helper (* e = K'[CmpXchg _ _ _] *)
    |iSolveTC
    |iSolveTC
    |iAssumptionCore || fail "tp_cmpxchg_suc: cannot find '? ↦ ?'"
    |try (simpl; congruence)     (* v' = v1 *)
    |try heap_lang.proofmode.solve_vals_cmpxchg_compare_safe
    |pm_reflexivity || fail "tp_cmpxchg_suc: this should not happen"
    |(* new goal *)]).

Lemma tac_tp_faa `{relocG Σ} j Δ1 Δ2 Δ3 E1 E2 ρ i1 i2 i3 p K' e (l : loc)  e2 (z1 z2 : Z) Q :
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (p, spec_ctx ρ) →
  envs_lookup_delete false i2 Δ1 = Some (false, j ⤇ e, Δ2)%I →
  e = fill K' (FAA #l e2) →
  IntoVal e2 #z2 →
  envs_lookup i3 Δ2 = Some (false, l ↦ₛ #z1)%I →
  envs_simple_replace i3 false
    (Esnoc (Esnoc Enil i2 (j ⤇ fill K' #z1)) i3 (l ↦ₛ #(z1+z2))%I) Δ2 = Some Δ3 →
  envs_entails Δ3 (|={E1,E2}=> Q) →
  envs_entails Δ1 (|={E1,E2}=> Q).
Proof.
  rewrite envs_entails_eq. intros ??? Hfill <- ?? HQ.
  rewrite -(idemp bi_and (of_envs Δ1)).
  rewrite {1}(envs_lookup_sound' Δ1 false). 2: eassumption.
  rewrite bi.sep_elim_l.
  enough (<pers> spec_ctx ρ ∧ of_envs Δ1 ={E1,E2}=∗ Q) as <-.
  { rewrite -bi.intuitionistically_into_persistently_1.
    destruct p; simpl;
    by rewrite ?(bi.intuitionistic_intuitionistically (spec_ctx ρ)). }
  rewrite bi.persistently_and_intuitionistically_sep_l.
  rewrite bi.intuitionistic_intuitionistically.
  rewrite envs_lookup_delete_sound // /=.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i3) //.
  simpl. rewrite right_id Hfill.
  (* (S (spec_ctx ρ) (S (j => fill _ _) (S (l ↦ v) ..))) *)
  rewrite (assoc _ (spec_ctx ρ) (j ⤇ fill K' _)%I).
  (* (S (S (spec_ctx ρ) (j => fill _ _)) (S (l ↦ v) ..)) *)
  rewrite assoc.
  rewrite -(assoc _ (spec_ctx ρ) (j ⤇ fill K' _)%I).
  rewrite step_faa //.
  rewrite -(fupd_trans E1 E1 E2).
  rewrite fupd_frame_r.
  apply fupd_mono.
  by rewrite (comm _ (j ⤇ _)%I) bi.wand_elim_r.
Qed.

Tactic Notation "tp_faa" constr(j) :=
  iStartProof;
  with_spec_ctx ltac:(fun _ =>
  eapply (tac_tp_faa j);
    [solve_ndisj || fail "tp_faa: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_faa: cannot find spec_ctx" (* spec_ctx *)
    |iAssumptionCore || fail "tp_faa: cannot find '" j " ⤇ ?'"
    |tp_bind_helper (* e = K'[FAA _ _ _] *)
    |iSolveTC (* IntoVal *)
    |iAssumptionCore || fail "tp_faa: cannot find '? ↦ ?'"
    |pm_reflexivity || fail "tp_faa: this should not happen"
    |(* new goal *)]).

Lemma tac_tp_fork `{relocG Σ} j Δ1 Δ2 E1 E2 ρ i1 i2 p K' e e' Q :
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (p, spec_ctx ρ) →
  envs_lookup i2 Δ1 = Some (false, j ⤇ e)%I →
  e = fill K' (Fork e') →
  envs_simple_replace i2 false
    (Esnoc Enil i2 (j ⤇ fill K' #())) Δ1 = Some Δ2 →
  envs_entails Δ2 (∀ (j' : nat), j' ⤇ e' -∗ |={E1,E2}=> Q)%I →
  envs_entails Δ1 (|={E1,E2}=> Q).
Proof.
  rewrite envs_entails_eq. intros ??? Hfill ? HQ.
  rewrite -(idemp bi_and (of_envs Δ1)).
  rewrite {1}(envs_lookup_sound' Δ1 false i1). 2: eassumption.
  rewrite bi.sep_elim_l /=.
  enough (<pers> spec_ctx ρ ∧ of_envs Δ1 ={E1,E2}=∗ Q) as <-.
  { rewrite -bi.intuitionistically_into_persistently_1.
    destruct p; simpl;
    by rewrite ?(bi.intuitionistic_intuitionistically (spec_ctx ρ)). }
  rewrite bi.persistently_and_intuitionistically_sep_l.
  rewrite bi.intuitionistic_intuitionistically.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i2) //; simpl.
  rewrite right_id Hfill.
  (* (S (spec_ctx ρ) (S (j => fill) (S (l ↦ v) ..))) *)
  rewrite (assoc _ (spec_ctx ρ) (j ⤇ _)%I).
  rewrite step_fork //.
  rewrite -(fupd_trans E1 E1 E2).
  rewrite fupd_frame_r.
  apply fupd_mono.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim. intros j'.
  rewrite (comm _ (j ⤇ _)%I (j' ⤇ _)%I).
  rewrite -assoc.
  rewrite bi.wand_elim_r.
  rewrite HQ.
  rewrite (bi.forall_elim j').
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_fork" constr(j) :=
  iStartProof;
  with_spec_ctx ltac:(fun _ =>
  eapply (tac_tp_fork j);
    [solve_ndisj || fail "tp_fork: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_fork: cannot find spec_ctx" (* spec_ctx *)
    |iAssumptionCore || fail "tp_fork: cannot find '" j " ⤇ ?'"
    |tp_bind_helper
    |pm_reflexivity || fail "tp_fork: this should not happen"
    |(* new goal *)]).

Tactic Notation "tp_fork" constr(j) "as" ident(j') constr(H) :=
  iStartProof;
  with_spec_ctx ltac:(fun _ =>
  eapply (tac_tp_fork j);
    [solve_ndisj || fail "tp_fork: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_fork: cannot find spec_ctx" (* spec_ctx *)
    |iAssumptionCore || fail "tp_fork: cannot find '" j " ⤇ ?'"
    |tp_bind_helper
    |pm_reflexivity || fail "tp_fork: this should not happen"
    |(iIntros (j') || fail 1 "tp_fork: " j' " not fresh ");
     (iIntros H || fail 1 "tp_fork: " H " not fresh")
    (* new goal *)]).

Tactic Notation "tp_fork" constr(j) "as" ident(j') :=
  let H := iFresh in tp_fork j as j' H.

Lemma tac_tp_alloc `{relocG Σ} j Δ1 E1 E2 ρ i1 i2 p K' e e' v Q :
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (p, spec_ctx ρ) →
  envs_lookup i2 Δ1 = Some (false, j ⤇ e)%I →
  e = fill K' (ref e') →
  IntoVal e' v →
  (∀ l : loc, ∃ Δ2,
    envs_simple_replace i2 false
       (Esnoc Enil i2 (j ⤇ fill K' #l)) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((l ↦ₛ v) -∗ |={E1,E2}=> Q)%I)) →
  envs_entails Δ1 (|={E1,E2}=> Q).
Proof.
  rewrite envs_entails_eq. intros ??? Hfill <- HQ.
  rewrite -(idemp bi_and (of_envs Δ1)).
  rewrite {1}(envs_lookup_sound' Δ1 false i1). 2: eassumption.
  rewrite bi.sep_elim_l /=.
  enough (<pers> spec_ctx ρ ∧ of_envs Δ1 ={E1,E2}=∗ Q) as <-.
  { rewrite -bi.intuitionistically_into_persistently_1.
    destruct p; simpl;
    by rewrite ?(bi.intuitionistic_intuitionistically (spec_ctx ρ)). }
  rewrite bi.persistently_and_intuitionistically_sep_l.
  rewrite bi.intuitionistic_intuitionistically.
  rewrite (envs_lookup_sound' Δ1 false i2). 2: eassumption.
  rewrite Hfill assoc /=.
  rewrite step_alloc //.
  rewrite -(fupd_trans E1 E1 E2).
  rewrite fupd_frame_r.
  apply fupd_mono.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim=> l.
  destruct (HQ l) as (Δ2 & HΔ2 & HQ').
  rewrite (envs_simple_replace_sound' _ _ i2 _ _ HΔ2).
  rewrite (comm _ (j ⤇ _)%I (l ↦ₛ _)%I).
  rewrite -assoc /= right_id.
  rewrite bi.wand_elim_r.
  rewrite HQ'.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "tp_alloc" constr(j) "as" ident(j') constr(H) :=
  let finish _ :=
      first [ intros j' | fail 1 "tp_alloc:" j' "not fresh"];
        eexists; split;
        [ pm_reflexivity
        | iIntros H || fail 1 "tp_alloc:" H "not correct intro pattern" ] in
  iStartProof;
  with_spec_ctx ltac:(fun _ =>
  eapply (tac_tp_alloc j);
    [solve_ndisj || fail "tp_alloc: cannot prove 'nclose specN ⊆ ?'"
    |iAssumptionCore || fail "tp_alloc: cannot find spec_ctx" (* spec_ctx *)
    |iAssumptionCore || fail "tp_alloc: cannot find '" j " ⤇ ?'"
    |tp_bind_helper
    |iSolveTC || fail "tp_alloc: expressions is not a value"
    |finish ()
    (* new goal *)]).

Tactic Notation "tp_alloc" constr(j) "as" ident(j') :=
  let H := iFresh in tp_alloc j as j' H.


(*
(**************************)
(* tp_apply *)

Fixpoint print_sel (ss : list sel_pat) (s : string) :=
  match ss with
  | nil => s
  | SelPure :: ss' => (String "%" (String " " (print_sel ss' s)))
  | SelPersistent :: ss' =>  (String "#" (print_sel ss' s))
  | SelSpatial :: ss' => (* no clue :( *) (print_sel ss' s)
  | SelIdent (INamed n) :: ss' => append n (String " " (print_sel ss' s))
  | SelIdent (IAnon _) :: ss' => String "?" (String " " (print_sel ss' s))
  (* wat to do with the index? *)
  end.

Ltac print_sel ss :=
  lazymatch type of ss with
  | list sel_pat => eval vm_compute in (print_sel ss "")
  | string => ss
  end.

Definition appP (ss : option (list sel_pat)) (Hj Hs : string) :=
  match ss with
  | Some ss' => cons (SelIdent Hs) (app ss' [SelIdent Hj])
  | None => cons (SelIdent Hs) [SelIdent Hj]
  end.

Definition add_elim_pat (pat : string) (Hj : string) :=
  match pat with
  | EmptyString => Hj
  | _ => append (String "[" (append Hj (String " " pat))) "]"
  end.

Tactic Notation "tp_apply" constr(j) open_constr(lem) "with" constr(Hs) "as" constr(Hr) :=
  iStartProof;
  let rec find Γ j :=
    match Γ with
    | Esnoc ?Γ (IAnon _) ?P =>
      find Γ j
    | Esnoc ?Γ (INamed ?Hj) ?P =>
      lazymatch P with
      | (j ⤇ _)%I => Hj
      | _ => find Γ j
      end
    | Enil => fail 2 "tp_apply: cannot find " j " ⤇ _ "
    | _ => fail 2 "tp_apply: unknown error in find"
    end in
  let rec findSpec Γp Γs :=
    match Γp with
    | Esnoc ?Γ (IAnon _) _ => findSpec Γ Γs
    | Esnoc ?Γ (INamed ?Hspec) ?P =>
      lazymatch P with
      | (spec_ctx _)%I => Hspec
      | _ => findSpec Γ Γs
      end
    | Enil =>
      match Γs with
      | Enil => fail 2 "tp_apply: cannot find spec_ctx _"
      | _ => findSpec Γs Enil
      end
    | _ => fail 2 "tp_apply: unknown error in findSpec"
    end in
  match goal with
  | |- envs_entails (Envs ?Γp ?Γs) ?Q =>
    let Hj := (find Γs j) in
    let Hspec := findSpec Γp Γs in
    let pat := eval vm_compute in (appP (sel_pat.parse Hs) Hj Hspec) in
    let pats := print_sel pat in
    let elim_pats := eval vm_compute in (add_elim_pat Hr Hj) in
    iMod (lem with pats) as elim_pats; first try by solve_ndisj
  | _ => fail "tp_apply: cannot parse the context"
  end.

Tactic Notation "tp_apply" constr(j) open_constr(lem) "with" constr(Hs) := tp_apply j lem with Hs as "".

Tactic Notation "tp_apply" constr(j) open_constr(lem) "as" constr(Hr) := tp_apply j lem with "" as Hr.

Tactic Notation "tp_apply" constr(j) open_constr(lem) := tp_apply j lem with "" as "".
*)
