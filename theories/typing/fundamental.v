(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Compatibility lemmas for the logical relation *)
From iris.heap_lang Require Import proofmode.
From reloc.logic Require Import model.
From reloc Require Export proofmode.
From reloc.typing Require Export interp.

From iris.proofmode Require Export tactics.
From Autosubst Require Import Autosubst.

Section fundamental.
  Context `{relocG Σ}.
  Implicit Types Δ : listC (lty2C Σ).
  Hint Resolve to_of_val.

  (** TODO: actually use this folding tactic *)
  (* right now it is not compatible with the _atomic tactics *)
  Local Ltac fold_logrel :=
    lazymatch goal with
    | |- environments.envs_entails _
         (refines ?E (fmap (λ τ, _ _ ?Δ) ?Γ) ?e1 ?e2 (_ (interp ?T) _)) =>
      fold (bin_log_related E Δ Γ e1 e2 T)
    end.

  Local Ltac intro_clause := progress (iIntros (vs) "#Hvs"; iSimpl).
  Local Ltac intro_clause' := progress (iIntros (?) "?"; iSimpl).
  Local Ltac value_case := try intro_clause';
    try rel_pure_l; try rel_pure_r; rel_values.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(Hv):=
    rel_bind_l (_ e1);
    rel_bind_r (_ e2);
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
    ({Δ;Γ} ⊨ e ≤log≤ e' : TProd τ1 τ2) -∗
    {Δ;Γ} ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v w "IH".
    iDestruct "IH" as (v1 v2 w1 w2) "(% & % & IHw & IHw')". simplify_eq/=.
    value_case.
  Qed.

  Lemma bin_log_related_snd Δ Γ e e' τ1 τ2 :
    ({Δ;Γ} ⊨ e ≤log≤ e' : TProd τ1 τ2) -∗
    {Δ;Γ} ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v w "IH".
    iDestruct "IH" as (v1 v2 w1 w2) "(% & % & IHw & IHw')". simplify_eq/=.
    value_case.
  Qed.

  Lemma bin_log_related_app Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ1) -∗
    {Δ;Γ} ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_app with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  (* TODO horrible horrible *)
  Lemma bin_log_related_rec Δ (Γ : stringmap type) (f x : binder) (e e' : expr) τ1 τ2 :
    □ ({Δ;<[f:=TArrow τ1 τ2]>(<[x:=τ1]>Γ)} ⊨ e ≤log≤ e' : τ2) -∗
    {Δ;Γ} ⊨ Rec f x e ≤log≤ Rec f x e' : TArrow τ1 τ2.
  Proof.
    iIntros "#Ht".
    intro_clause.
    rel_pure_l. rel_pure_r.
    iApply refines_arrow_val.
    iModIntro. iLöb as "IH". iIntros (v1 v2) "#Hτ1".
    rel_pure_l. rel_pure_r.
    iApply refines_spec_ctx. iDestruct 1 as (ρ) "#Hs".

    set (r := (RecV f x (subst_map (binder_delete x (binder_delete f (fst <$> vs))) e), RecV f x (subst_map (binder_delete x (binder_delete f (snd <$> vs))) e'))).
    set (vvs' := binder_insert f r (binder_insert x (v1,v2) vs)).
    iSpecialize ("Ht" $! vvs' with "[#]").
    { rewrite !binder_insert_fmap.
      iApply (env_ltyped2_insert with "[IH]").
      - iApply (interp_arrow_val with "Hs").
        fold interp. (* ?? *)
        iAlways. iApply "IH".
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
    iApply refines_fork; first solve_ndisj.
    by iApply "IH".
  Qed.

  Lemma bin_log_related_tlam Δ Γ (e e' : expr) τ :
    (∀ (A : lty2 Σ),
      □ ({(A::Δ);⤉Γ} ⊨ e ≤log≤ e' : τ)) -∗
    {Δ;Γ} ⊨ (Λ: e) ≤log≤ (Λ: e') : TForall τ.
  Proof.
    iIntros "#H".
    (* TODO: here it is also better to use some sort of characterization
       of the semantic type for forall *)
    intro_clause.
    iApply refines_spec_ctx. iDestruct 1 as (ρ) "#Hs".
    value_case. rewrite /lty2_forall /lty2_car /=.
    iModIntro. iModIntro. iIntros (A) "!>". iIntros (? ?) "_".

    rewrite /bin_log_related refines_eq /refines_def.
    iDestruct ("H" $! A) as "#H1".
    iSpecialize ("H1" with "[Hvs]").
    { by rewrite (interp_ren A Δ Γ). }

    iIntros (j K) "Hj /=".
    iModIntro. tp_pure j _. wp_pures. simpl.

    iMod ("H1" with "Hs Hj") as "$".
  Qed.

  Lemma bin_log_related_tapp' Δ Γ e e' τ τ' :
    ({Δ;Γ} ⊨ e ≤log≤ e' : TForall τ) -∗
    {Δ;Γ} ⊨ (TApp e) ≤log≤ (TApp e') : τ.[τ'/].
  Proof.
    (* TODO: here it is also better to use some sort of characterization
       of the semantic type for forall *)
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    iSpecialize ("IH" $! (interp τ' Δ)).
    rewrite interp_val_arrow. iDestruct "IH" as "#IH".
    iSpecialize ("IH" $! #() #() with "[//]").
    by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_tapp (τi : lty2 Σ) Δ Γ e e' τ :
    ({Δ;Γ} ⊨ e ≤log≤ e' : TForall τ) -∗
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
    rel_bind_l (_ e1).
    rel_bind_r (_ e1').
    iApply (refines_bind _ _ _ (interp τ1 (R :: Δ)) with "[He1] [He2]").
    - iApply ("He1" with "[Hvs]").
      by rewrite interp_ren.
    - iIntros (? ?) "? /=".
      repeat rel_pure_l. repeat rel_pure_r.
      by iApply "He2".
  Qed.

  (* TODO
  Lemma bin_log_related_seq' Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Δ;Γ} ⊨ (e1;; e2) ≤log≤ (e1';; e2') : τ2.
  Proof.
    iIntros "He1 He2".
    iApply (bin_log_related_seq (λne _, True%I) _ _ _ _ _ _ τ1.[ren (+1)] with "[He1]"); auto.
    by iApply bin_log_related_weaken_2.
  Qed. *)

  Lemma bin_log_related_injl Δ Γ e e' τ1 τ2 :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ1) -∗
    {Δ;Γ} ⊨ InjL e ≤log≤ InjL e' : (TSum τ1 τ2).
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "Hvv".
    value_case. iExists _,_. eauto.
  Qed.

  Lemma bin_log_related_injr Δ Γ e e' τ1 τ2 :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ2) -∗
    {Δ;Γ} ⊨ InjR e ≤log≤ InjR e' : TSum τ1 τ2.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "Hvv".
    value_case. iExists _,_. eauto.
  Qed.

  Lemma bin_log_related_case Δ Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 :
    ({Δ;Γ} ⊨ e0 ≤log≤ e0' : TSum τ1 τ2) -∗
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : TArrow τ1 τ3) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : TArrow τ2 τ3) -∗
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
    rel_bind_ap e e' "IH" v v' "IH".
    iDestruct "IH" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    rel_load_l_atomic.
    iInv (relocN .@ "ref" .@ (l,l')) as (w w') "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    iModIntro. iExists _; iFrame "Hw1".
    iNext. iIntros "Hw1".
    rel_load_r.
    iMod ("Hclose" with "[Hw1 Hw2]").
    { iNext. iExists w,w'; by iFrame. }
    value_case.
  Qed.

  Lemma bin_log_related_store Δ Γ e1 e2 e1' e2' τ :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : (Tref τ)) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    {Δ;Γ} ⊨ Store e1 e2 ≤log≤ Store e1' e2' : TUnit.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    rel_bind_ap e2 e2' "IH2" w w' "IH2".
    rel_bind_ap e1 e1' "IH1" v v' "IH1".
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    rel_store_l_atomic.
    iInv (relocN .@ "ref" .@ (l,l')) as (v v') "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro. iExists _; iFrame "Hv1".
    iNext. iIntros "Hw1".
    rel_store_r.
    iMod ("Hclose" with "[Hw1 Hv2 IH2]").
    { iNext; iExists _, _; simpl; iFrame. }
    value_case.
  Qed.

  Lemma bin_log_related_CAS Δ Γ e1 e2 e3 e1' e2' e3' τ
    (HEqτ : EqType τ)
    (HUbτ : UnboxedType τ) :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : Tref τ) -∗
    ({Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    ({Δ;Γ} ⊨ e3 ≤log≤ e3' : τ) -∗
    {Δ;Γ} ⊨ CAS e1 e2 e3 ≤log≤ CAS e1' e2' e3' : TBool.
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
    simplify_eq. rel_cas_l_atomic.
    iInv (relocN .@ "ref" .@ (l,l')) as (v1 v1') "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro. iExists _; iFrame. simpl.
    destruct (decide (v1 = v2')) as [|Hneq]; subst.
    - iSplitR; first by (iIntros (?); contradiction).
      iIntros (?). iNext. iIntros "Hv1".
      iDestruct (eq_type_sound with "Hv") as "%"; first fast_done.
      rel_cas_suc_r.
      iMod ("Hclose" with "[-]").
      { iNext; iExists _, _; by iFrame. }
      rel_values.
    - iSplitL; last by (iIntros (?); congruence).
      iIntros (?). iNext. iIntros "Hv1".
      iDestruct (eq_type_sound with "Hv") as "%"; first fast_done.
      rel_cas_fail_r.
      iMod ("Hclose" with "[-]").
      { iNext; iExists _, _; by iFrame. }
      rel_values.
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
    ({Δ;Γ} ⊨ e ≤log≤ e' : TRec τ) -∗
    {Δ;Γ} ⊨ rec_unfold e ≤log≤ rec_unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    iEval (rewrite lty_rec_unfold /lty2_car /=) in "IH".
    change (lty2_rec _) with (interp (TRec τ) Δ).
    unfold rec_unfold. unlock. (* TODO WHY?????? *)
    rel_pure_l. rel_pure_r.
    value_case. by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_fold Δ Γ e e' τ :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ.[(TRec τ)/]) -∗
    {Δ;Γ} ⊨ e ≤log≤ e' : TRec τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "IH".
    value_case.
    iModIntro.
    iEval (rewrite lty_rec_unfold /lty2_car /=).
    change (lty2_rec _) with (interp (TRec τ) Δ).
    by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_pack' Δ Γ e e' (τ τ' : type) :
    ({Δ;Γ} ⊨ e ≤log≤ e' : τ.[τ'/]) -∗
    {Δ;Γ} ⊨ e ≤log≤ e' : TExists τ.
  Proof.
    iIntros "IH".
    intro_clause.
    rel_bind_ap e e' "IH" v v' "#IH".
    value_case.
    iModIntro. iExists (interp τ' Δ).
    by rewrite interp_subst.
  Qed.

  Lemma bin_log_related_pack (τi : lty2 Σ) Δ Γ e e' τ :
    ({τi::Δ;⤉Γ} ⊨ e ≤log≤ e' : τ) -∗
    {Δ;Γ} ⊨ e ≤log≤ e' : TExists τ.
  Proof.
    iIntros "IH".
    intro_clause.
    iSpecialize ("IH" $! vs with "[Hvs]").
    { by rewrite interp_ren. }
    rel_bind_ap e e' "IH" v v' "#IH".
    value_case.
    iModIntro. by iExists τi.
  Qed.

(*
  Lemma bin_log_related_unpack Δ Γ e1 e1' e2 e2' τ τ2 :
    ({Δ;Γ} ⊨ e1 ≤log≤ e1' : TExists τ) -∗
    (∀ τi : lty2 Σ,
      {τi::Δ;⤉Γ} ⊨
        e2 ≤log≤ e2' : TArrow τ (subst (ren (+1)) τ2)) -∗
    {Δ;Γ} ⊨ unpack e1 e2 ≤log≤ unpack e1' e2' : τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    Abort.
    iSpecialize ("IH2" $! vs with "[Hvs]").
    { by rewrite interp_ren. }
    rel_bind_ap e2 e2' "IH2" v v' "#IH2".
*)

  Theorem binary_fundamental Δ Γ e τ :
    Γ ⊢ₜ e : τ → ({Δ;Γ} ⊨ e ≤log≤ e : τ)%I.
  Proof.
    intros Ht. iInduction Ht as [] "IH" forall (Δ).
    - by iApply bin_log_related_var.
    - iApply bin_log_related_unit.
    - by iApply bin_log_related_nat.
    - by iApply bin_log_related_bool.
    - by iApply (bin_log_related_nat_binop with "[]").
    - by iApply (bin_log_related_bool_binop with "[]").
    - by iApply bin_log_related_ref_binop.
    - by iApply (bin_log_related_pair with "[]").
    - by iApply bin_log_related_fst.
    - by iApply bin_log_related_snd.
    - by iApply bin_log_related_injl.
    - by iApply bin_log_related_injr.
    - by iApply (bin_log_related_case with "[] []").
    - by iApply (bin_log_related_if with "[] []").
    - iApply (bin_log_related_rec with "[]"); eauto.
    - by iApply (bin_log_related_app with "[] []").
    - iApply bin_log_related_tlam; eauto.
    - by iApply bin_log_related_tapp'.
    - by iApply bin_log_related_fold.
    - by iApply bin_log_related_unfold.
    - by iApply bin_log_related_pack'.
    (* - iApply (bin_log_related_unpack with "[]"); eauto. *)
    - by iApply bin_log_related_fork.
    - by iApply bin_log_related_alloc.
    - by iApply bin_log_related_load.
    - by iApply (bin_log_related_store with "[]").
    - by iApply (bin_log_related_CAS with "[] []").
  Qed.

End fundamental.
