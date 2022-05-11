(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Assorted facts about operational semantics. *)
From iris.program_logic Require Import language.

Section facts.
  Context {Λ : language}.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types tp : list (expr Λ).

  Lemma erased_step_nonempty tp σ tp' σ'  :
    erased_step (tp, σ) (tp', σ') → tp' ≠ [].
  Proof.
    intros [? Hs].
    destruct Hs as [e1 σ1' e2 σ2' efs tp1 tp2 ?? Hstep]; simplify_eq/=.
    intros [_ HH]%app_eq_nil. by inversion HH.
  Qed.

  Lemma rtc_erased_step_nonempty tp σ tp' σ'  :
    rtc erased_step (tp, σ) (tp', σ') → tp ≠ [] → tp' ≠ [].
  Proof.
    pose (P := λ (x y : list (expr Λ) * (state Λ)), x.1 ≠ [] → y.1 ≠ []).
    eapply (rtc_ind_r_weak P).
    - intros [tp2 σ2]. unfold P. naive_solver.
    - intros [tp1 σ1] [tp2 σ2] [tp3 σ3]. unfold P; simpl.
      intros ? ?%erased_step_nonempty. naive_solver.
  Qed.


  Lemma erased_step_ectx e e' tp tp' σ σ' K `{!LanguageCtx K} :
    erased_step (e :: tp, σ) (e' :: tp', σ') →
    erased_step ((K e) :: tp, σ) (K e' :: tp', σ').
  Proof.
    intros [κ Hst]. inversion Hst; simplify_eq/=.
    destruct t1 as [|h1 t1]; simplify_eq/=.
    { simplify_eq/=.
      eapply fill_step in H1. simpl in H1.
      econstructor. eapply step_atomic with (t1 := []); eauto. }
    econstructor. econstructor; eauto.
    + rewrite app_comm_cons. reflexivity.
    + rewrite app_comm_cons. reflexivity.
  Qed.

  Local Definition ffill K `{!LanguageCtx K} :
    (list (expr Λ) * (state Λ)) → (list (expr Λ) * (state Λ)) :=
    fun x => match x with
             | (e :: tp, σ) => (K e :: tp, σ)
             | ([], σ) => ([], σ)
             end.

  Lemma rtc_erased_step_ectx e e' tp tp' σ σ' K `{!LanguageCtx K} :
    rtc erased_step (e :: tp, σ) (e' :: tp', σ') →
    rtc erased_step (K e :: tp, σ) (K e' :: tp', σ').
  Proof.
    change (rtc erased_step (K e :: tp, σ) (K e' :: tp', σ'))
      with (rtc erased_step (ffill K (e :: tp, σ)) (ffill K (e' :: tp', σ'))).
    eapply (rtc_congruence (ffill K) erased_step).
    clear e e' tp tp' σ σ'.
    intros [tp σ] [tp' σ'].
    destruct tp as [|e tp].
    - inversion 1. inversion H0. exfalso.
      simplify_eq/=. by eapply app_cons_not_nil.
    - intros Hstep1.
      assert (tp' ≠ []).
      { eapply (rtc_erased_step_nonempty (e::tp)).
        econstructor; naive_solver.
        naive_solver. }
      destruct tp' as [|e' tp']; first naive_solver.
      simpl. by eapply erased_step_ectx.
  Qed.

  Lemma nice_ctx_lemma' K tp1 tp2 e ρ1 ρ2 v `{!LanguageCtx K} :
    ρ1.1 = (K e) :: tp1 →
    ρ2.1 = of_val v :: tp2 →
    rtc erased_step ρ1 ρ2 →
    ∃ tp2' tp3' σ' σ'' w,
      rtc erased_step (e :: tp1, ρ1.2) (of_val w :: tp2', σ') ∧
      rtc erased_step (K (of_val w) :: tp2', σ') (of_val v :: tp3', σ'').
  Proof.
    intros Heq1 Heq2 Hsteps.
    revert tp1 e Heq1 Heq2.
    induction Hsteps as [ρ|ρ1 ρ2 ρ3 Hstep Hsteps IH];
      intros tp1 e Hρ1 Hρ2.
    { destruct (to_val e) as [w|] eqn:He.
      - apply of_to_val in He as <-.
        destruct ρ as [ρ1 ρ2]. simplify_eq/=.
        eexists _, _, _, _, w. split; first reflexivity.
        rewrite H. reflexivity.
    - assert (to_val (K e) = None) by auto using fill_not_val.
      destruct ρ as [ρ1 ρ2]. simplify_eq/=.
      assert (of_val v = K e) as ?%of_to_val_flip; naive_solver. }
    destruct Hstep as [κs [e1 σ1 e2 σ2 efs t1 t2 -> -> Hstep]]; simpl in *.
    destruct t1 as [|h1 t1]; simplify_eq/=.
    - destruct (to_val e) as [w|] eqn:He.
      + apply of_to_val in He as <-.
        destruct ρ3 as [ρ3_1 ρ3_2]. simplify_eq/=.
        eexists _, _, _, _, w. split; first reflexivity.
        econstructor; last eassumption.
        econstructor. eapply step_atomic with (t1:=[]); eauto.
      + apply fill_step_inv in Hstep as (e2'&->&Hstep); last done.
        specialize (IH (tp1++efs) e2').
        assert (K e2' :: tp1 ++ efs = K e2' :: tp1 ++ efs) as H1 by done.
        specialize (IH H1 Hρ2).
        destruct IH as (tp2'&tp3'&σ'&σ''&w&[Hsteps1 Hsteps2]).
        eexists _,_,_,_,w. split; last eassumption.
        eapply rtc_l, Hsteps1.
        exists κs. by eapply step_atomic with (t1:=[]).
    - specialize (IH (t1 ++ e2 :: t2 ++ efs) e).
      assert (K e :: t1 ++ e2 :: t2 ++ efs = K e :: t1 ++ e2 :: t2 ++ efs) as H1 by done.
    specialize (IH H1 Hρ2).
    destruct IH as (tp2'&tp3'&σ'&σ''&w&Hsteps1&Hstep2).
    eexists _,_,_,_,w. split; last eassumption.
    eapply rtc_l, Hsteps1.
    exists κs. econstructor; rewrite ?app_comm_cons; done.
  Qed.

  Lemma nice_ctx_lemma K tp1 tp2 e σ1 σ2 v `{!LanguageCtx K} :
    rtc erased_step (K e :: tp1, σ1) (of_val v :: tp2, σ2) →
    ∃ tp2' tp3' σ' σ'' w,
      rtc erased_step (e :: tp1, σ1) (of_val w :: tp2', σ') ∧
      rtc erased_step (K (of_val w) :: tp2', σ') (of_val v :: tp3', σ'').
  Proof. by eapply nice_ctx_lemma'. Qed.

  Lemma nice_ctx_lemma_1 K tp1 tp2 e σ1 σ2 v `{!LanguageCtx K} :
    rtc erased_step (K e :: tp1, σ1) (of_val v :: tp2, σ2) →
    ∃ tp2' σ' w,
      rtc erased_step (e :: tp1, σ1) (of_val w :: tp2', σ').
  Proof.
    intros Hρ.
    cut (∃ tp2' tp3' σ' σ'' w,
      rtc erased_step (e :: tp1, σ1) (of_val w :: tp2', σ') ∧
      rtc erased_step (K (of_val w) :: tp2', σ') (of_val v :: tp3', σ'')).
    { naive_solver. }
    eapply nice_ctx_lemma; eauto.
  Qed.

  Local Ltac inv_step :=
    match goal with
    | [ H : erased_step _ _ |- _ ] => inversion H; clear H; simplify_eq/=; inv_step
    | [ H : step _ _ _ |- _ ] => inversion H; clear H; simplify_eq/=
    end.

  Lemma pure_exec_inversion_lemma' tp1 tp2 e1 e2 ρ1 ρ2 v ϕ :
    ρ1.1 = e1 :: tp1 →
    ρ2.1 = of_val v :: tp2 →
    PureExec ϕ 1 e1 e2 →
    ϕ →
    rtc erased_step ρ1 ρ2 →
    rtc erased_step (e2 :: tp1, ρ1.2) ρ2.
  Proof.
    intros Heq1 Heq2 Hpure Hϕ Hsteps.
    revert tp1 Heq1 Heq2. specialize (Hpure Hϕ).
    apply nsteps_once_inv in Hpure.
    revert e1 Hpure.
    induction Hsteps as [ρ|ρ1 ρ2 ρ3 Hstep Hsteps IH]; intros e1 Hpure tp1 Hρ1 Hρ2.
    - destruct ρ as [ρ_1 ρ_2]. simplify_eq/=.
      assert (Inhabited (state Λ)).
      { refine (populate ρ_2). }
      assert (to_val e2 = Some v) as He2.
      { by apply rtc_pure_step_val, rtc_once. }
      apply of_to_val in He2. subst. naive_solver.
    - destruct ρ1 as [? σ1].
      destruct ρ2 as [tp σ2].
      destruct ρ3 as [? σ3].
      simplify_eq/=.
      inv_step.
      destruct t1 as [|h1 t1]; simplify_eq/=.
      + eapply pure_step_det in H2; last done.
        destruct_and!; simplify_eq/=. by rewrite app_nil_r in Hsteps.
      + specialize (IH h1 Hpure (t1 ++ e3 :: t2 ++ efs) eq_refl eq_refl).
        etrans; last by apply IH.
        eapply rtc_once. econstructor.
        by eapply (step_atomic _ _ _ _ efs (e2::t1)).
  Qed.

  Lemma pure_exec_inversion_lemma tp1 tp2 e1 e2 σ1 σ2 v ϕ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    rtc erased_step (e1 :: tp1, σ1) (of_val v :: tp2, σ2) →
    rtc erased_step (e2 :: tp1, σ1) (of_val v :: tp2, σ2).
  Proof. by eapply pure_exec_inversion_lemma'. Qed.

  Lemma pure_exec_erased_step tp e1 e2 σ ϕ :
    PureExec ϕ 1 e1 e2 →
    ϕ →
    erased_step (e1 :: tp, σ) (e2 :: tp, σ).
  Proof.
    intros Hpure Hϕ. specialize (Hpure Hϕ).
    apply nsteps_once_inv in Hpure.
    econstructor. eapply step_atomic with (t1:=[]) (efs:=[]); eauto.
    { by rewrite app_nil_r. }
    destruct (pure_step_safe _ _ Hpure σ) as (e2' & σ' & efs & Hstep).
    destruct (pure_step_det _ _ Hpure _ _ _ _ _ Hstep).
    naive_solver.
  Qed.

End facts.
