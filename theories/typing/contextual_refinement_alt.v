From Autosubst Require Import Autosubst.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics.
From reloc.prelude Require Import lang_facts.
From reloc.typing Require Export contextual_refinement.

(* Alternative formulation of contextual refinement
without restricting to contexts of the ground type *)
Definition ctx_refines_alt (Γ : stringmap type)
    (e e' : expr) (τ : type) : Prop := ∀ K thp σ₀ σ₁ v1 τ',
  typed_ctx K Γ τ ∅ τ' →
  rtc erased_step ([fill_ctx K e], σ₀) (of_val v1 :: thp, σ₁) →
  ∃ thp' σ₁' v2, rtc erased_step ([fill_ctx K e'], σ₀) (of_val v2 :: thp', σ₁').


Lemma ctx_refines_impl_alt Γ e1 e2 τ :
  (Γ ⊨ e1 ≤ctx≤ e2 : τ) →
  ctx_refines_alt Γ e1 e2 τ.
Proof.
  intros H C thp σ0 σ1 v1 τ' HC Hstep.
  pose (C' := (CTX_AppR (λ: <>, #true)%E)::C).
  cut (∃ (thp' : list expr) σ₁',
              rtc erased_step ([fill_ctx C' e2], σ0)
                (of_val #true :: thp', σ₁')).
  - unfold C'; simpl.
    destruct 1 as (thp' & σ1' & Hstep').
    eapply (nice_ctx_lemma_1 (fill [AppRCtx (λ: <>, #true)]) []).
    { apply _. }
    eapply Hstep'.
  - eapply (H C' thp _ σ1 true).
    + repeat econstructor; eauto.
    + unfold C'. simpl.
      trans (((of_val v1) ;; #true)%E :: thp, σ1); last first.
      { econstructor.
        - econstructor.
          eapply (step_atomic) with (t1 := []); try reflexivity.
          eapply Ectx_step with (K:=[AppLCtx v1]); try reflexivity.
          econstructor.
        - eapply rtc_once. rewrite app_nil_r. econstructor.
          eapply (step_atomic) with (efs:=[]) (t1 := []); try reflexivity.
          { rewrite /= app_nil_r //. }
          eapply Ectx_step with (K:=[]); try reflexivity.
          by econstructor. }
      pose (K := [AppRCtx (λ: <>, #true)%E]).
      change (fill_ctx C e1;; #true)%E with (fill K (fill_ctx C e1)).
      change (v1;; #true)%E with (fill K (of_val v1)).
      by eapply rtc_erased_step_ectx; first by apply _.
Qed.

(* In order to prove the other direction we need a couple of auxiliary
definitions *)

Definition bot : val := rec: "bot" <> := "bot" #().
Definition assert_ : val :=
  λ: "v", if: "v" then #() else bot #().

Local Ltac inv_step :=
  match goal with
  | [ H : erased_step _ _ |- _ ] => inversion H; clear H; simplify_eq/=; inv_step
  | [ H : step _ _ _ |- _ ] => inversion H; clear H; simplify_eq/=
  end.
Local Ltac inv_rtc_step :=
  match goal with
  | [ H : rtc erased_step _ _ |- _ ] =>
    inversion H as [|? [? ?] ? ?];
    clear H; simplify_eq/=
  end.
Local Ltac solve_pure_exec :=
  match goal with
  | |- PureExec _ _ ?e1 _ =>
    reshape_expr e1 ltac:(fun K e =>
      eapply (pure_exec_ctx (fill K)); apply _)
  end.

Local Ltac side_cond_solver := unfold vals_compare_safe; naive_solver.

Lemma rtc_erased_step_bot v tp1 tp2 σ1 σ2:
  rtc erased_step (bot #() :: tp1, σ1) (of_val v :: tp2, σ2) →
  False.
Proof.
  intros [n Hsteps]%rtc_nsteps_1. revert tp1 σ1 Hsteps.
  induction (lt_wf n) as [n IH1 IH]=>tp1 σ1 Hsteps. destruct n as [|m].
  - inversion Hsteps.
  - inversion Hsteps; simplify_eq/=.
    destruct y.
    inv_step. destruct t1 as [|h1 t1]; simplify_eq/=.
    + assert (PureExec True 1 (bot (of_val #())) (bot (of_val #()))).
      { unfold bot.
        assert (((rec: "bot" <> := "bot" #())%V #())
                  = subst' <> #() (subst' "bot" bot ("bot" #()))) as HH.
        { reflexivity. }
        rewrite {2}HH. eapply pure_beta.
        unfold bot. apply _. }
      eapply pure_step_det in H3; last first.
      { apply nsteps_once_inv. by eapply pure_exec. }
      destruct_and!. simplify_eq/=.
      eapply IH; eauto.
    + eapply (IH m (lt_n_Sn m) (t1 ++ e2 :: t2 ++ efs)); eauto.
Qed.

Lemma ctx_refines_alt_impl Γ e1 e2 τ :
  ctx_refines_alt Γ e1 e2 τ →
  (Γ ⊨ e1 ≤ctx≤ e2 : τ).
Proof.
  intros Href C thp σ0 σ1 b HC Hstep.
  pose (C' := [CTX_AppR (of_val assert_); CTX_BinOpL EqOp #b]).
  assert (typed_ctx (C'++C) Γ τ ∅ TUnit) as Htyped.
  { eapply typed_ctx_compose; eauto.
    econstructor.
    { econstructor. unfold assert_.
      repeat econstructor; eauto. }
    econstructor; last by econstructor.
    econstructor; eauto. repeat econstructor; eauto. }
  pose (K := [BinOpLCtx EqOp #b; AppRCtx assert_]).
  assert (∃ thp' σ', rtc erased_step ([fill_ctx (C'++C) e1], σ0)
              (of_val #() :: thp', σ')) as (thp1'&σ1'&Hassert1).
  { simpl.
    change (∃ (thp' : list expr) (σ' : state),
               rtc erased_step ([fill K (fill_ctx C e1)], σ0) (of_val #() :: thp', σ')).
    eexists _,_. trans (fill K (of_val #b) :: thp, σ1).
    - eapply rtc_erased_step_ectx; eauto. apply _.
    - simpl. econstructor.
      + eapply pure_exec_erased_step ; [ solve_pure_exec | side_cond_solver ].
      + simpl. rewrite bool_decide_eq_true_2 //.
        econstructor.
        * unfold assert_.
          eapply pure_exec_erased_step ; [ solve_pure_exec | side_cond_solver ].
        * simpl. eapply rtc_once.
          eapply pure_exec_erased_step ; [ solve_pure_exec | naive_solver ]. }
  assert (∃ thp' σ' v2, rtc erased_step ([fill_ctx (C'++C) e2], σ0)
              (of_val v2 :: thp', σ')) as (thp2'&σ2'&v2&Hassert2).
  { eapply Href; eauto. }
  simpl in Hassert2.
  destruct (nice_ctx_lemma (fill K) [] _ (fill_ctx C e2) σ0 _ v2 Hassert2)
    as (tp2'&tp3'&σ3'&σ4'&w&Hw1&Hw2).
  simpl in Hw2.
  cut (w = #b); first by naive_solver.
  revert Hw2. clear. intros Hw2.
  eapply pure_exec_inversion_lemma in Hw2; [ | solve_pure_exec | side_cond_solver ].
  simpl in Hw2. unfold assert_ in Hw2.
  eapply pure_exec_inversion_lemma in Hw2; [ | solve_pure_exec | side_cond_solver ].
  simpl in Hw2.
  case_bool_decide; eauto. exfalso.
  eapply pure_exec_inversion_lemma in Hw2; [ | solve_pure_exec | side_cond_solver ].
  simpl in Hw2.
  by eapply rtc_erased_step_bot.
Qed.

