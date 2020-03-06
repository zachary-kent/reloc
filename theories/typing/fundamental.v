(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Compatibility lemmas for the logical relation *)
From Autosubst Require Import Autosubst.
From iris.heap_lang Require Import proofmode.
From reloc.logic Require Import model.
From reloc.logic Require Export rules derived compatibility proofmode.tactics.
From reloc.typing Require Export interp.
From iris.proofmode Require Export tactics.

Section fundamental.
  Context `{relocG Σ}.
  Implicit Types Δ : listO (lrelC Σ).
  Hint Resolve to_of_val : core.

  Local Ltac intro_clause := progress (iIntros (vs) "#Hvs /=").
  Local Ltac intro_clause' := progress (iIntros (?) "? /=").
  Local Ltac value_case := try intro_clause';
    try rel_pure_l; try rel_pure_r; rel_values.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(Hv):=
    rel_bind_l (subst_map _ e1);
    rel_bind_r (subst_map _ e2);
    try iSpecialize (IH with "Hvs");
    iApply (refines_bind with IH);
    iIntros (v w) Hv; simpl.

  Lemma bin_log_related_var Δ Γ x τ :
    Γ !! x = Some τ →
    {Δ;Γ} ⊨ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros (Hx). iIntros (vs) "#Hvs". simpl.
    rewrite (env_ltyped2_lookup _ vs x); last first.
    { rewrite lookup_fmap Hx //. }
    rewrite !lookup_fmap.
    iDestruct "Hvs" as (v1 v2 ->) "HA". simpl.
    by iApply refines_ret.
  Qed.

  Lemma bin_log_related_unit Δ Γ : {Δ;Γ} ⊨ #() ≤log≤ #() : TUnit.
  Proof. value_case. Qed.

  Lemma bin_log_related_nat Δ Γ (n : nat) : {Δ;Γ} ⊨ #n ≤log≤ #n : TNat.
  Proof. value_case. Qed.

  Lemma bin_log_related_bool Δ Γ (b : bool) : {Δ;Γ} ⊨ #b ≤log≤ #b : TBool.
  Proof. value_case. Qed.

  Lemma bin_log_related_pair Δ Γ e1 e2 e1' e2' (τ1 τ2 : type) :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Δ;Γ} ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_pair with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_fst Δ Γ e e' τ1 τ2 :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ1 * τ2) -∗
    {Δ;Γ} ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v w "IH".
    iDestruct "IH" as (v1 v2 w1 w2) "(% & % & IHw & IHw')". simplify_eq/=.
    value_case.
  Qed.

  Lemma bin_log_related_snd Δ Γ e e' τ1 τ2 :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ1 * τ2) -∗
    {Δ;Γ} ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v w "IH".
    iDestruct "IH" as (v1 v2 w1 w2) "(% & % & IHw & IHw')". simplify_eq/=.
    value_case.
  Qed.

  Lemma bin_log_related_app Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1 → τ2) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ1) -∗
    {Δ;Γ} ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_app with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_rec Δ (Γ : stringmap type) (f x : binder) (e e' : expr) τ1 τ2 :
    □ ({Δ;<[f:=TArrow τ1 τ2]>(<[x:=τ1]>Γ)} ⊨ e ≤log≤ e' : τ2) -∗
    {Δ;Γ} ⊨ Rec f x e ≤log≤ Rec f x e' : τ1 → τ2.
  Proof.
    iIntros "#Ht".
    intro_clause.
    rel_pure_l. rel_pure_r.
    iApply refines_arrow_val.
    iModIntro. iLöb as "IH". iIntros (v1 v2) "#Hτ1".
    rel_pure_l. rel_pure_r.
    iApply refines_spec_ctx. iIntros "#Hs".

    set (r := (RecV f x (subst_map (binder_delete x (binder_delete f (fst <$> vs))) e), RecV f x (subst_map (binder_delete x (binder_delete f (snd <$> vs))) e'))).
    set (vvs' := binder_insert f r (binder_insert x (v1,v2) vs)).
    iSpecialize ("Ht" $! vvs' with "[#]").
    { rewrite !binder_insert_fmap.
      iApply (env_ltyped2_insert with "[IH]").
      - iApply "IH".
      - iApply (env_ltyped2_insert with "Hτ1").
        by iFrame. }

    unfold vvs'.
    destruct x as [|x], f as [|f];
      rewrite /= ?fmap_insert ?subst_map_insert //;
      try by iApply "H".
    destruct (decide (x = f)) as [->|]; iSimpl in "Ht".
    - rewrite !delete_insert_delete !subst_subst !delete_idemp.
      by iApply "Ht".
    - rewrite !delete_insert_ne // subst_map_insert.
      rewrite !(subst_subst_ne _ x f) // subst_map_insert.
      by iApply "Ht".
  Qed.

  Lemma bin_log_related_fork Δ Γ e e' :
    ({Δ;Γ} ⊨ e ≤log≤ e' : TUnit) -∗
    {Δ;Γ} ⊨ Fork e ≤log≤ Fork e' : TUnit.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_fork.
    by iApply "IH".
  Qed.

  Lemma bin_log_related_tlam Δ Γ (e e' : expr) τ :
    (∀ (A : lrel Σ),
      □ ({(A::Δ);⤉Γ} ⊨ e ≤log≤ e' : τ)) -∗
    {Δ;Γ} ⊨ (Λ: e) ≤log≤ (Λ: e') : ∀: τ.
  Proof.
    iIntros "#H".
    intro_clause. rel_pure_l. rel_pure_r.
    iApply refines_forall.
    iModIntro. iIntros (A).
    iDestruct ("H" $! A) as "#H1".
    iApply "H1".
    by rewrite (interp_ren A Δ Γ).
  Qed.

  Lemma bin_log_related_tapp' Δ Γ e e' τ τ' :
    ({Δ;Γ} ⊨ e ≤log≤ e' : ∀: τ) -∗
    {Δ;Γ} ⊨ (TApp e) ≤log≤ (TApp e') : τ.[τ'/].
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    iSpecialize ("IH" $! (interp τ' Δ)).
    iDestruct "IH" as "#IH".
    iSpecialize ("IH" $! #() #() with "[//]").
    by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_tapp (τi : lrel Σ) Δ Γ e e' τ :
    ({Δ;Γ} ⊨ e ≤log≤ e' : ∀: τ) -∗
    {τi::Δ;⤉Γ} ⊨ (TApp e) ≤log≤ (TApp e') : τ.
  Proof.
    iIntros "IH". intro_clause.
    iApply (bin_log_related_app _ _ e #() e' #() TUnit τ with "[IH] [] Hvs").
    - iClear (vs) "Hvs". intro_clause.
      rewrite interp_ren.
      iSpecialize ("IH" with "Hvs").
      iApply (refines_wand with "IH").
      eauto with iFrame.
    - value_case.
  Qed.

  Lemma bin_log_related_seq R Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({(R::Δ);⤉Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Δ;Γ} ⊨ (e1;; e2) ≤log≤ (e1';; e2') : τ2.
  Proof.
    iIntros "He1 He2".
    intro_clause.
    iApply (refines_seq (interp τ1 (R::Δ)) with "[He1]").
    - iApply ("He1" with "[Hvs]").
      by rewrite interp_ren.
    - by iApply "He2".
  Qed.

  Lemma bin_log_related_seq' Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Δ;Γ} ⊨ (e1;; e2) ≤log≤ (e1';; e2') : τ2.
  Proof.
    iIntros "He1 He2".
    iApply (bin_log_related_seq lrel_true _ _ _ _ _ _ τ1.[ren (+1)%nat] with "[He1] He2").
    intro_clause.
    rewrite interp_ren -(interp_ren_up [] Δ τ1).
    by iApply "He1".
  Qed.

  Lemma bin_log_related_injl Δ Γ e e' τ1 τ2 :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ1) -∗
    {Δ;Γ} ⊨ InjL e ≤log≤ InjL e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "Hvv".
    value_case. iExists _,_. eauto.
  Qed.

  Lemma bin_log_related_injr Δ Γ e e' τ1 τ2 :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ2) -∗
    {Δ;Γ} ⊨ InjR e ≤log≤ InjR e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "Hvv".
    value_case. iExists _,_. eauto.
  Qed.

  Lemma bin_log_related_case Δ Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 :
    ({Δ;Γ} ⊨ e0 ≤log≤ e0' : τ1 + τ2) -∗
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1 → τ3) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2 → τ3) -∗
    {Δ;Γ} ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause.
    rel_bind_ap e0 e0' "IH1" v0 v0' "IH1".
    iDestruct "IH1" as (w w') "[(% & % & #Hw)|(% & % & #Hw)]"; simplify_eq/=;
      rel_case_l; rel_case_r.
    - iApply (bin_log_related_app Δ Γ _ w _ w'  with "IH2 [] Hvs").
      value_case.
    - iApply (bin_log_related_app Δ Γ _ w _ w'  with "IH3 [] Hvs").
      value_case.
  Qed.

  Lemma bin_log_related_if Δ Γ e0 e1 e2 e0' e1' e2' τ :
    ({Δ;Γ} ⊨ e0 ≤log≤ e0' : TBool) -∗
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : τ) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    {Δ;Γ} ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause.
    rel_bind_ap e0 e0' "IH1" v0 v0' "IH1".
    iDestruct "IH1" as ([]) "[% %]"; simplify_eq/=;
      rel_if_l; rel_if_r.
    - by iApply "IH2".
    - by iApply "IH3".
  Qed.

  Lemma bin_log_related_load Δ Γ e e' τ :
    ({Δ;Γ} ⊨ e ≤log≤ e' : (Tref τ)) -∗
    {Δ;Γ} ⊨ Load e ≤log≤ Load e' : τ.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_load.
    by iApply "IH".
  Qed.

  Lemma bin_log_related_store Δ Γ e1 e2 e1' e2' τ :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : Tref τ) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    {Δ;Γ} ⊨ Store e1 e2 ≤log≤ Store e1' e2' : TUnit.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_store with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_FAA Δ Γ e1 e2 e1' e2' :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : Tref TNat) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : TNat) -∗
    {Δ;Γ} ⊨ FAA e1 e2 ≤log≤ FAA e1' e2' : TNat.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 e2' "IH2" v2 v2' "#IH2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "#IH1".
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    iDestruct "IH2" as (n) "[% %]". simplify_eq.
    rel_apply_l refines_faa_l.
    iInv (relocN .@ "ref" .@ (l,l')) as (v1 v1') "[Hv1 [>Hv2 #>Hv]]" "Hclose".
    iDestruct "Hv" as (n1) "[% %]"; simplify_eq.
    iModIntro. iExists _; iFrame. iNext.
    iIntros "Hl".
    (* TODO: tactics for these operations *)
    rel_apply_r (refines_faa_r with "Hv2"). iIntros "Hv2".
    iMod ("Hclose" with "[-]") as "_".
    { iNext. iExists _,_. iFrame. iExists _; iSplit; eauto. }
    rel_values.
  Qed.

  Lemma bin_log_related_CmpXchg Δ Γ e1 e2 e3 e1' e2' e3' τ
    (HEqτ : EqType τ)
    (HUbτ : UnboxedType τ) :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : Tref τ) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    ({Δ;Γ} ⊨ e3 ≤log≤ e3' : τ) -∗
    {Δ;Γ} ⊨ CmpXchg e1 e2 e3 ≤log≤ CmpXchg e1' e2' e3' : TProd τ TBool.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause.
    rel_bind_ap e3 e3' "IH3" v3 v3' "#IH3".
    rel_bind_ap e2 e2' "IH2" v2 v2' "#IH2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "#IH1".
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    iDestruct (unboxed_type_sound with "IH2") as "[% %]"; try fast_done.
    iDestruct (eq_type_sound with "IH2") as "%"; first fast_done.
    iDestruct (eq_type_sound with "IH3") as "%"; first fast_done.
    simplify_eq. rel_cmpxchg_l_atomic.
    iInv (relocN .@ "ref" .@ (l,l')) as (v1 v1') "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro. iExists _; iFrame. simpl.
    destruct (decide (v1 = v2')) as [|Hneq]; subst.
    - iSplitR; first by (iIntros (?); contradiction).
      iIntros (?). iNext. iIntros "Hv1".
      iDestruct (eq_type_sound with "Hv") as "%"; first fast_done.
      rel_cmpxchg_suc_r.
      iMod ("Hclose" with "[-]").
      { iNext; iExists _, _; by iFrame. }
      rel_values. iExists _, _, _, _. do 2 (iSplitL; first done).
      iFrame "Hv". iExists _. done.
    - iSplitL; last by (iIntros (?); congruence).
      iIntros (?). iNext. iIntros "Hv1".
      iDestruct (eq_type_sound with "Hv") as "%"; first fast_done.
      rel_cmpxchg_fail_r.
      iMod ("Hclose" with "[-]").
      { iNext; iExists _, _; by iFrame. }
      rel_values. iExists _, _, _, _. do 2 (iSplitL; first done).
      iFrame "Hv". iExists _. done.
  Qed.

  Lemma bin_log_related_alloc Δ Γ e e' τ :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ) -∗
    {Δ;Γ} ⊨ Alloc e ≤log≤ Alloc e' : Tref τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    rel_alloc_l l as "Hl".
    rel_alloc_r k as "Hk".
    iMod (inv_alloc (relocN .@ "ref" .@ (l,k)) _ (∃ w1 w2,
      l ↦ w1 ∗ k ↦ₛ w2 ∗ interp τ Δ w1 w2)%I with "[Hl Hk IH]") as "HN"; eauto.
    { iNext. iExists v, v'; simpl; iFrame. }
    rel_values. iExists l, k. eauto.
  Qed.

  Lemma bin_log_related_ref_binop Δ Γ e1 e2 e1' e2' τ :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : Tref τ) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : Tref τ) -∗
    {Δ;Γ} ⊨ BinOp EqOp e1 e2 ≤log≤ BinOp EqOp e1' e2' : TBool.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 e2' "IH2" v2 v2' "#IH2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "#IH1".
    iDestruct "IH1" as (l1 l2) "[% [% #Hl]]"; simplify_eq/=.
    iDestruct "IH2" as (l1' l2') "[% [% #Hl']]"; simplify_eq/=.
    rel_op_l. rel_op_r.
    destruct (decide (l1 = l1')) as [->|?].
    - iMod (interp_ref_funct _ _ l1' l2 l2' with "[Hl Hl']") as %->.
      { solve_ndisj. }
      { iSplit; iExists _,_; eauto. }
      rewrite !bool_decide_true //.
      value_case.
    - destruct (decide (l2 = l2')) as [->|?].
      + iMod (interp_ref_inj _ _ l2' l1 l1' with "[Hl Hl']") as %->.
        { solve_ndisj. }
        { iSplit; iExists _,_; eauto. }
        congruence.
      + rewrite !bool_decide_false //; try congruence.
        value_case.
  Qed.

  Lemma bin_log_related_nat_binop Δ Γ op e1 e2 e1' e2' τ :
    binop_nat_res_type op = Some τ →
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : TNat) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : TNat) -∗
    {Δ;Γ} ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 e2' "IH2" v2 v2' "IH2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "IH1".
    iDestruct "IH1" as (n) "[% %]"; simplify_eq/=.
    iDestruct "IH2" as (n') "[% %]"; simplify_eq/=.
    destruct (binop_nat_typed_safe op n n' _ Hopτ) as [v' Hopv'].
    rel_op_l; eauto.
    rel_op_r; eauto.
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma bin_log_related_bool_binop Δ Γ op e1 e2 e1' e2' τ :
    binop_bool_res_type op = Some τ →
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : TBool) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : TBool) -∗
    {Δ;Γ} ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 e2' "IH2" v2 v2' "IH2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "IH1".
    iDestruct "IH1" as (n) "[% %]"; simplify_eq/=.
    iDestruct "IH2" as (n') "[% %]"; simplify_eq/=.
    destruct (binop_bool_typed_safe op n n' _ Hopτ) as [v' Hopv'].
    rel_op_l; eauto.
    rel_op_r; eauto.
    value_case.
    destruct op; inversion Hopv'; simplify_eq/=; eauto.
  Qed.

  Lemma bin_log_related_unfold Δ Γ e e' τ :
    ({Δ;Γ} ⊨ e ≤log≤ e' : μ: τ) -∗
    {Δ;Γ} ⊨ rec_unfold e ≤log≤ rec_unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    iEval (rewrite lrel_rec_unfold /lrel_car /=) in "IH".
    change (lrel_rec _) with (interp (TRec τ) Δ).
    rel_rec_l. rel_rec_r.
    value_case. by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_fold Δ Γ e e' τ :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ.[(TRec τ)/]) -∗
    {Δ;Γ} ⊨ e ≤log≤ e' : μ: τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    value_case.
    iModIntro.
    iEval (rewrite lrel_rec_unfold /lrel_car /=).
    change (lrel_rec _) with (interp (TRec τ) Δ).
    by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_pack' Δ Γ e e' (τ τ' : type) :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ.[τ'/]) -∗
    {Δ;Γ} ⊨ e ≤log≤ e' : ∃: τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "#IH".
    value_case.
    iModIntro. iExists (interp τ' Δ).
    by rewrite interp_subst.
  Qed.

  Lemma bin_log_related_pack (τi : lrel Σ) Δ Γ e e' τ :
    ({τi::Δ;⤉Γ} ⊨ e ≤log≤ e' : τ) -∗
    {Δ;Γ} ⊨ e ≤log≤ e' : ∃: τ.
  Proof.
    iIntros "IH".
    intro_clause.
    iSpecialize ("IH" $! vs with "[Hvs]").
    { by rewrite interp_ren. }
    rel_bind_ap e e' "IH" v v' "#IH".
    value_case.
    iModIntro. by iExists τi.
  Qed.

  Lemma bin_log_related_unpack Δ Γ x e1 e1' e2 e2' τ τ2 :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : ∃: τ) -∗
    (∀ τi : lrel Σ,
      {τi::Δ;<[x:=τ]>(⤉Γ)} ⊨
        e2 ≤log≤ e2' : (Autosubst_Classes.subst (ren (+1)%nat) τ2)) -∗
    {Δ;Γ} ⊨ (unpack: x := e1 in e2) ≤log≤ (unpack: x := e1' in e2') : τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    rel_pure_l. rel_pure_r.
    rel_bind_ap e1 e1' "IH1" v v' "#IH1".
    iDestruct "IH1" as (A) "#IH".
    rel_rec_l. rel_pure_l. rel_pure_l.
    rel_rec_r. rel_pure_r. rel_pure_r.
    rel_pure_l. rel_pure_r.
    iSpecialize ("IH2" $! A (binder_insert x (v,v') vs) with "[Hvs]").
    { rewrite -(interp_ren A).
      rewrite binder_insert_fmap.
      iApply (env_ltyped2_insert with "IH Hvs"). }
    rewrite !binder_insert_fmap !subst_map_binder_insert /=.
    iApply (refines_wand with "IH2").
    iIntros (v1 v2). rewrite (interp_ren_up [] Δ τ2 A).
    asimpl. eauto.
  Qed.

  Theorem fundamental Δ Γ e τ :
    Γ ⊢ₜ e : τ → ({Δ;Γ} ⊨ e ≤log≤ e : τ)%I
  with fundamental_val Δ v τ :
    ⊢ᵥ v : τ → (interp τ Δ v v).
  Proof.
    - intros Ht. destruct Ht.
      + by iApply bin_log_related_var.
      + iIntros (γ) "#H". simpl. rel_values.
        iModIntro. by iApply fundamental_val.
      + iApply bin_log_related_unit.
      + by iApply bin_log_related_nat.
      + by iApply bin_log_related_bool.
      + iApply bin_log_related_nat_binop; first done;
          by iApply fundamental.
      + iApply bin_log_related_bool_binop; first done;
          by iApply fundamental.
      + iApply bin_log_related_ref_binop;
          by iApply fundamental.
      + iApply bin_log_related_pair;
          by iApply fundamental.
      + iApply bin_log_related_fst;
          by iApply fundamental.
      + iApply bin_log_related_snd;
          by iApply fundamental.
      + iApply bin_log_related_injl;
          by iApply fundamental.
      + iApply bin_log_related_injr;
          by iApply fundamental.
      + iApply bin_log_related_case;
          by iApply fundamental.
      + iApply bin_log_related_if;
          by iApply fundamental.
      + iApply bin_log_related_rec.
        iAlways. by iApply fundamental.
      + iApply bin_log_related_app;
          by iApply fundamental.
      + iApply bin_log_related_tlam.
        iIntros (A). iAlways. by iApply fundamental.
      + iApply bin_log_related_tapp'; by iApply fundamental.
      + iApply bin_log_related_fold; by iApply fundamental.
      + iApply bin_log_related_unfold; by iApply fundamental.
      + iApply bin_log_related_pack'; by iApply fundamental.
      + iApply bin_log_related_unpack; try by iApply fundamental.
        iIntros (A). by iApply fundamental.
      + iApply bin_log_related_fork; by iApply fundamental.
      + iApply bin_log_related_alloc; by iApply fundamental.
      + iApply bin_log_related_load; by iApply fundamental.
      + iApply bin_log_related_store; by iApply fundamental.
      + iApply bin_log_related_FAA; eauto;
          by iApply fundamental.
      + iApply bin_log_related_CmpXchg; eauto;
          by iApply fundamental.
    - intros Hv. destruct Hv; simpl.
      + iSplit; eauto.
      + iExists _; iSplit; eauto.
      + iExists _; iSplit; eauto.
      + iExists _,_,_,_.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iExists _,_. iLeft.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iExists _,_. iRight.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iLöb as "IH". iAlways.
        iIntros (v1 v2) "#Hv".
        pose (Γ := (<[f:=(τ1 → τ2)%ty]> (<[x:=τ1]> ∅)):stringmap type).
        pose (γ := (binder_insert f ((rec: f x := e)%V,(rec: f x := e)%V)
                     (binder_insert x (v1, v2) ∅)):stringmap (val*val)).
        rel_pure_l. rel_pure_r.
        iPoseProof (fundamental Δ Γ e τ2 $! γ with "[]") as "H"; eauto.
        { rewrite /γ /Γ. rewrite !binder_insert_fmap fmap_empty.
          iApply (env_ltyped2_insert with "IH").
          iApply (env_ltyped2_insert with "Hv").
          iApply env_ltyped2_empty. }
        rewrite /γ /=. rewrite !binder_insert_fmap !fmap_empty /=.
        by rewrite !subst_map_binder_insert_2_empty.
      + iIntros (A). iAlways. iIntros (v1 v2) "_".
        rel_pures_l. rel_pures_r.
        iPoseProof (fundamental (A::Δ) ∅ e τ $! ∅ with "[]") as "H"; eauto.
        { rewrite fmap_empty. iApply env_ltyped2_empty. }
        by rewrite !fmap_empty subst_map_empty.
  Qed.

  Theorem refines_typed τ Δ e :
    ∅ ⊢ₜ e : τ →
    REL e << e : (interp τ Δ ).
  Proof.
    move=> /fundamental Hty.
    iPoseProof (Hty Δ with "[]") as "H".
    { rewrite fmap_empty. iApply env_ltyped2_empty. }
    by rewrite !fmap_empty !subst_map_empty.
  Qed.

End fundamental.
