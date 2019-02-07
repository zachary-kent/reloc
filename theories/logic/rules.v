(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Core ReLoC rules *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import list.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Import proofmode.
From reloc.logic Require Import model proofmode.spec_tactics.
From reloc.prelude Require Import ctx_subst pureclosed.

Section rules.
  Context `{relocG Σ}.
  Implicit Types A : lty2 Σ.
  Implicit Types e t : expr.
  Implicit Types v w : val.

  (** * Primitive rules *)

  (** ([fupd_logrel] is defined in [logrel_binary.v]) *)

  (** ** Forward reductions on the LHS *)

  Lemma refines_pure_l Γ n
    (K' : list ectx_item) e e' t A ϕ :
    PureClosed ϕ n e e' →
    ϕ →
    ▷^n (Γ ⊨ fill K' e' << t : A)
    ⊢ Γ ⊨ fill K' e << t : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (vvs ρ) "#Hs HΓ"; iIntros (j K) "Hj /=".
    rewrite subst_map_fill.
    iApply wp_pure_step_later; [ | apply Hϕ | ].
    { apply pure_exec_ctx; first apply _.
      apply pureexec_subst_map. }
    iModIntro. iNext. iApply fupd_wp.
    iSpecialize ("IH" with "Hs HΓ Hj").
    by rewrite subst_map_fill.
  Qed.

  Lemma refines_masked_l E Γ n
    (K' : list ectx_item) e e' t A ϕ :
    PureClosed ϕ n e e' →
    ϕ →
    ({E;Γ} ⊨ fill K' e' << t : A)
    ⊢ {E;Γ} ⊨ fill K' e << t : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (vvs ρ) "#Hs HΓ"; iIntros (j K) "Hj /=".
    rewrite subst_map_fill.
    iApply wp_pure_step_later; [ | apply Hϕ | ].
    { apply pure_exec_ctx; first apply _.
      apply pureexec_subst_map. }
    iMod ("IH" with "Hs HΓ Hj") as "IH".
    iModIntro. iNext.
    by rewrite subst_map_fill.
  Qed.

  Lemma refines_wp_l Γ K e1 e2 A :
    is_closed_expr' e1 →
    (WP e1 {{ v,
        Γ ⊨ fill K (of_val v) << e2 : A }})%I -∗
    Γ ⊨ fill K e1 << e2 : A.
  Proof.
    rewrite refines_eq /refines_def =>Hclosed.
    iIntros "He".
    iIntros (vvs ρ) "#Hs HΓ". iIntros (j K') "Hj /=".
    rewrite subst_map_fill Hclosed //.
    iModIntro. iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    iMod ("Hv" with "Hs [HΓ] Hj"); auto.
    by rewrite subst_map_fill /=.
  Qed.

  Lemma refines_atomic_l Γ (E : coPset) K e1 e2 A
        (Hatomic : Atomic WeaklyAtomic e1) :
    is_closed_expr' e1 →
   (|={⊤,E}=> WP e1 @ E {{ v,
     {E;Γ} ⊨ fill K (of_val v) << e2 : A }})%I -∗
   Γ ⊨ fill K e1 << e2 : A.
  Proof.
    rewrite refines_eq /refines_def => Hclosed.
    iIntros "Hlog".
    iIntros (vvs ρ) "#Hs HΓ". iIntros (j K') "Hj /=". iModIntro.
    rewrite subst_map_fill Hclosed //.
    iApply (wp_bind (fill (subst_map_ctx _ K))).
    iApply wp_atomic; auto.
    iMod "Hlog" as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    iSpecialize ("Hlog" with "Hs [HΓ]"); first by iFrame.
    iSpecialize ("Hlog" with "Hj"). simpl.
    rewrite subst_map_fill //.
  Qed.

  (** ** Forward reductions on the RHS *)

  Lemma refines_pure_r Γ E K' e e' t A n
    (Hspec : nclose specN ⊆ E) ϕ :
    PureClosed ϕ n e e' →
    ϕ →
    ({E;Γ} ⊨ t << fill K' e' : A)
    ⊢ {E;Γ} ⊨ t << fill K' e : A.
  Proof.
    rewrite refines_eq /refines_def => Hpure Hϕ.
    iIntros "Hlog". iIntros (vvs ρ) "#Hs HΓ". iIntros (j K) "Hj /=".
    rewrite subst_map_fill -fill_app.
    assert (PureExec ϕ n (subst_map (snd <$> vvs) e) (subst_map (snd <$> vvs) e')).
    { apply pureexec_subst_map. }
    tp_pure j _; auto.
    rewrite fill_app -subst_map_fill.
    iApply ("Hlog" with "Hs HΓ Hj").
  Qed.

  Lemma refines_step_r Φ Γ E K' e1 e2 A :
    is_closed_expr' e2 →
    (∀ ρ j K, spec_ctx ρ -∗ (j ⤇ fill K e2 ={E}=∗ ∃ v, j ⤇ fill K (of_val v)
                  ∗ Φ v)) -∗
    (∀ v, Φ v -∗ {E;Γ} ⊨ e1 << fill K' (of_val v) : A) -∗
    {E;Γ} ⊨ e1 << fill K' e2 : A.
  Proof.
    rewrite refines_eq /refines_def=> Hclosed.
    iIntros "He Hlog".
    iIntros (vvs ρ) "#Hs HΓ". iIntros (j K) "Hj /=".
    rewrite subst_map_fill -fill_app Hclosed //.
    iMod ("He" $! ρ j with "Hs Hj") as (v) "[Hj Hv]".
    iSpecialize ("Hlog" $! v with "Hv Hs HΓ").
    rewrite fill_app subst_map_fill.
    by iApply "Hlog".
  Qed.

  Lemma refines_alloc_r Γ E K e v t A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e v →
    (∀ l : loc, l ↦ₛ v -∗ {E;Γ} ⊨ t << fill K (of_val #l) : A)%I
    -∗ {E;Γ} ⊨ t << fill K (ref e) : A.
  Proof.
    intros <-.
    iIntros "Hlog".
    pose (Φ := (fun w => ∃ l : loc, ⌜w = (# l)⌝ ∗ l ↦ₛ v)%I).
    iApply (refines_step_r Φ); simpl; auto.
    { cbv[Φ].
      iIntros (ρ j K') "#Hs Hj /=".
      tp_alloc j as l "Hl". iExists (# l).
      iFrame. iExists l. eauto. }
    iIntros (v') "He'". iDestruct "He'" as (l) "[% Hl]". subst.
    by iApply "Hlog".
  Qed.

  Lemma refines_load_r Γ E K l q v t A
    (Hmasked : nclose specN ⊆ E) :
    l ↦ₛ{q} v -∗
    (l ↦ₛ{q} v -∗ {E;Γ} ⊨ t << fill K (of_val v) : A)
    -∗ {E;Γ} ⊨ t << (fill K !#l) : A.
  Proof.
    iIntros "Hl Hlog".
    pose (Φ := (fun w => ⌜w = v⌝ ∗ l ↦ₛ{q} v)%I).
    iApply (refines_step_r Φ with "[Hl]"); eauto.
    { cbv[Φ].
      iIntros (ρ j K') "#Hs Hj /=". iExists v.
      tp_load j.
      iFrame. eauto. }
    iIntros (?) "[% Hl]"; subst.
    by iApply "Hlog".
  Qed.

  Lemma refines_store_r Γ E K l e e' v v' A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e' v' →
    l ↦ₛ v -∗
    (l ↦ₛ v' -∗ {E;Γ} ⊨ e << fill K (of_val #()) : A) -∗
    {E;Γ} ⊨ e << fill K (#l <- e') : A.
  Proof.
    iIntros (<-) "Hl Hlog".
    pose (Φ := (fun w => ⌜w = #()⌝ ∗ l ↦ₛ v')%I).
    iApply (refines_step_r Φ with "[Hl]"); eauto.
    { cbv[Φ].
      iIntros (ρ j K') "#Hs Hj /=". iExists #().
      tp_store j.
      iFrame. eauto. }
    iIntros (w) "[% Hl]"; subst.
    by iApply "Hlog".
  Qed.

  Lemma refines_cas_fail_r Γ E K l e1 e2 v1 v2 v t A :
    nclose specN ⊆ E →
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    vals_cas_compare_safe v v1 →
    v ≠ v1 →
    l ↦ₛ v -∗
    (l ↦ₛ v -∗ {E;Γ} ⊨ t << fill K (of_val #false) : A)
    -∗ {E;Γ} ⊨ t << fill K (CAS #l e1 e2) : A.
  Proof.
    iIntros (?<-<-??) "Hl Hlog".
    pose (Φ := (fun (w : val) => ⌜w = #false⌝ ∗ l ↦ₛ v)%I).
    iApply (refines_step_r Φ with "[Hl]"); eauto.
    { cbv[Φ].
      iIntros (ρ j K') "#Hs Hj /=".
      tp_cas_fail j; auto.
      iExists #false. simpl.
      iFrame. eauto. }
    iIntros (w) "[% Hl]"; subst.
    by iApply "Hlog".
  Qed.

  Lemma refines_cas_suc_r Γ E K l e1 e2 v1 v2 v t A :
    nclose specN ⊆ E →
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    val_is_unboxed v1 →
    v = v1 →
    l ↦ₛ v -∗
    (l ↦ₛ v2 -∗ {E;Γ} ⊨ t << fill K (of_val #true) : A)
    -∗ {E;Γ} ⊨ t << fill K (CAS #l e1 e2) : A.
  Proof.
    iIntros (?<-<-??) "Hl Hlog".
    pose (Φ := (fun w => ⌜w = #true⌝ ∗ l ↦ₛ v2)%I).
    iApply (refines_step_r Φ with "[Hl]"); eauto.
    { cbv[Φ].
      iIntros (ρ j K') "#Hs Hj /=".
      tp_cas_suc j; auto.
      iExists #true. simpl.
      iFrame. eauto. }
    iIntros (w) "[% Hl]"; subst.
    by iApply "Hlog".
  Qed.

  Lemma refines_faa_r Γ E K l e2 (i1 i2 : Z) t A :
    nclose specN ⊆ E →
    IntoVal e2 #i2 →
    l ↦ₛ #i1 -∗
    (l ↦ₛ #(i1+i2) -∗ {E;Γ} ⊨ t << fill K (of_val #i1) : A)
    -∗ {E;Γ} ⊨ t << fill K (FAA #l e2) : A.
  Proof.
    iIntros (?<-) "Hl Hlog".
    pose (Φ := (fun w => ⌜w = #i1⌝ ∗ l ↦ₛ #(i1+i2))%I).
    iApply (refines_step_r Φ with "[Hl]"); eauto.
    { cbv[Φ].
      iIntros (ρ j K') "#Hs Hj /=".
      tp_faa j; auto.
      iExists #i1. simpl.
      iFrame. eauto. }
    iIntros (w) "[% Hl]"; subst.
    by iApply "Hlog".
  Qed.

  Lemma refines_fork_r Γ E K (e t : expr) A
   (Hmasked : nclose specN ⊆ E)
   (Hclosed : is_closed_expr [] e) :
   (∀ i, i ⤇ e -∗
     {E;Γ} ⊨ t << fill K (of_val #()) : A) -∗
   {E;Γ} ⊨ t << fill K (Fork e) : A.
  Proof.
    iIntros "Hlog".
    pose (Φ := (fun (v : val) => ∃ i, i ⤇ e ∗ ⌜v = #()⌝%V)%I).
    iApply (refines_step_r Φ with "[]"); cbv[Φ].
    { intros. by apply subst_map_is_closed_nil. }
    { iIntros (ρ j K') "#Hspec Hj".
      tp_fork j as i "Hi".
      iModIntro. iExists #(). iFrame. eauto.
    }
    iIntros (v). iDestruct 1 as (i) "[Hi %]"; subst.
    by iApply "Hlog".
  Qed.

  (** ** Primitive structural rules *)
  Lemma refines_spec_ctx Γ E e e' A :
    ((∃ ρ, spec_ctx ρ) -∗ {E;Γ} ⊨ e << e' : A) -∗
    ({E;Γ} ⊨ e << e' : A).
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hctx". iIntros (vvs ρ') "#Hspec".
    rewrite -(bi.intuitionistic_intuitionistically (spec_ctx _)).
    rewrite (bi.intuitionistically_sep_dup (spec_ctx _)).
    iDestruct "Hspec" as "[#Hspec #Hspec']".
    iRevert "Hspec'".
    rewrite (bi.intuitionistic_intuitionistically (spec_ctx _)).
    iAssert (∃ ρ, spec_ctx ρ)%I as "Hρ".
    { eauto. }
    iClear "Hspec".
    iRevert (vvs ρ').
    by iApply "Hctx".
  Qed.

  Lemma refines_var Γ x A :
    Γ !! x = Some A →
    Γ ⊨ Var x << Var x : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros (? vvs ρ) "#Hs #HΓ"; iIntros (j K) "Hj".
    iDestruct (env_ltyped2_lookup with "HΓ") as (v1 v2) "[H Hvv]"; first eassumption.
    iDestruct "H" as %Hvvs.
    simpl. rewrite !lookup_fmap !Hvvs /=.
    iModIntro. iApply wp_value. iExists _; by iFrame.
  Qed.

  Lemma refines_rec Γ (f x : binder) e e' A A' :
    □(binder_insert f (A → A')%lty2 (binder_insert x A Γ) ⊨ e << e' : A') -∗
    Γ ⊨ (rec: f x := e) << (rec: f x := e') : (A → A')%lty2.
  Proof.
    iIntros "#H".
    rewrite refines_eq /refines_def.
    iIntros (vvs ρ) "#Hρ #HΓ /=".
    iIntros (j K) "Hj". iModIntro.
    tp_pure j _. wp_pure _.
    iExists _. iFrame. iLöb as "IH".
    iAlways. iIntros (v1 v2) "#HA". clear j K.
    iIntros (j K) "Hj". iModIntro. wp_pures. tp_rec j.

    set (r := (RecV f x (subst_map (binder_delete x (binder_delete f (fst <$> vvs))) e), RecV f x (subst_map (binder_delete x (binder_delete f (snd <$> vvs))) e'))).
    set (vvs' := binder_insert f r (binder_insert x (v1,v2) vvs)).
    iSpecialize ("H" $! vvs' with "Hρ [#]").
    { iApply (env_ltyped2_insert with "IH").
      iApply (env_ltyped2_insert with "HA").
      by iFrame. }

    iSpecialize ("H" $! j K). iApply fupd_wp.
    unfold vvs'.
    destruct x as [|x], f as [|f];
      rewrite /= ?fmap_insert ?subst_map_insert //;
      try by iApply "H".
    destruct (decide (x = f)) as [->|]; iSimpl in "H".
    - rewrite !delete_insert_delete !subst_subst !delete_idemp.
      by iApply "H".
    - rewrite !delete_insert_ne // subst_map_insert.
      rewrite !(subst_subst_ne _ x f) // subst_map_insert.
      by iApply "H".
  Qed.

  Lemma refines_fork Γ e e' :
    (Γ ⊨ e << e' : ()%lty2) -∗
    Γ ⊨ Fork e << Fork e' : ().
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "H".
    iIntros (vvs ρ) "#Hs HΓ"; iIntros (j K) "Hj /=".
    tp_fork j as i "Hi". iModIntro.
    iSpecialize ("H" with "Hs HΓ").
    iSpecialize ("H" $! i [] with "Hi"). simpl.
    iApply (wp_fork with "[H]").
    - iNext. iMod "H". iApply (wp_wand with "H"). eauto.
    - iNext. iExists _. by iFrame.
  Qed.

  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val Γ (f x f' x' : binder) e e' eb eb' A A' :
    e = (RecV f x eb)%E →
    e' = (RecV f' x' eb')%E →
    □(∀ v1 v2, A v1 v2 -∗
      Γ ⊨ App e (of_val v1) << App e' (of_val v2) : A') -∗
    Γ ⊨ e << e' : (A → A')%lty2.
  Proof.
    iIntros (??) "#H".
    subst e e'. rewrite refines_eq.
    (* This is not a consequence of `refines_ret'.
       For a counterexample, consider a paradoxical [Γ = x :⊥] *)
    iIntros (vvs ρ) "#Hs #HΓ"; iIntros (j K) "Hj". simpl.
    iModIntro. iApply wp_value. iExists _; iFrame.
    iAlways. iIntros (v1 v2) "Hvv".
    iApply ("H" $! v1 v2 with "Hvv Hs HΓ").
  Qed.

  (* TODO *)
  (* Lemma interp_val_arrow (A A' : lty2) (v v' : val) ρ : *)
  (*   spec_ctx ρ -∗ *)
  (*   (A → A')%lty2 v v' *)
  (*             ∗-∗ *)
  (*   (□ (∀ (w w' : val), A w w' *)
  (*     -∗ ∅ ⊨ v w << v' w' : A'))%I. *)
  (* Proof. Abort. *)

  (** * Some derived (symbolic execution) rules *)

  (** ** Stateful reductions on the LHS *)

  Lemma refines_fork_l K Γ E e t A :
    is_closed_expr [] e →
   (|={⊤,E}=> ▷ (WP e {{ _, True }} ∗
    ({E;Γ} ⊨ fill K (of_val #()) << t : A))) -∗
   Γ ⊨ fill K (Fork e) << t : A.
  Proof.
    iIntros (?) "Hlog".
    iApply refines_atomic_l; auto.
    { intro. by apply subst_map_is_closed_nil. }
    iMod "Hlog" as "[Hsafe Hlog]". iModIntro.
    iApply (wp_fork with "Hsafe"). eauto.
  Qed.

  Lemma refines_alloc_l K Γ E e v t A :
    IntoVal e v →
    (|={⊤,E}=> ▷ (∀ l : loc, l ↦ v -∗
           {E;Γ} ⊨ fill K (of_val #l) << t : A))%I
    -∗ Γ ⊨ fill K (ref e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog". iModIntro.
    iApply (wp_alloc _ _ v); auto.
  Qed.

  Lemma refines_load_l K Γ E l q t A :
    (|={⊤,E}=> ∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ ({E;Γ} ⊨ fill K (of_val v') << t : A)))%I
    -∗ Γ ⊨ fill K (! #l) << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v') "[Hl Hlog]". iModIntro.
    iApply (wp_load with "Hl"); auto.
  Qed.

  Lemma refines_store_l K Γ E l e v' t A :
    IntoVal e v' →
    (|={⊤,E}=> ∃ v, ▷ l ↦ v ∗
      ▷(l ↦ v' -∗ {E;Γ} ⊨ fill K (of_val #()) << t : A))
    -∗ Γ ⊨ fill K (#l <- e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v) "[Hl Hlog]". iModIntro.
    iApply (wp_store _ _ _ _ v' with "Hl"); auto.
  Qed.

  Lemma refines_cas_l K Γ E l e1 e2 v1 v2 t A :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    val_is_unboxed v1 →
    (|={⊤,E}=> ∃ v', ▷ l ↦ v' ∗
     (⌜v' ≠ v1⌝ -∗ ▷ (l ↦ v' -∗ {E;Γ} ⊨ fill K (of_val #false) << t : A)) ∧
     (⌜v' = v1⌝ -∗ ▷ (l ↦ v2 -∗ {E;Γ} ⊨ fill K (of_val #true) << t : A)))
    -∗ Γ ⊨ fill K (CAS #l e1 e2) << t : A.
  Proof.
    iIntros (<-<-?) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v') "[Hl Hlog]". iModIntro.
    destruct (decide (v' = v1)).
    - (* CAS successful *) subst.
      iApply (wp_cas_suc with "Hl"); eauto.
      { by left. }
      iDestruct "Hlog" as "[_ Hlog]".
      iSpecialize ("Hlog" with "[]"); eauto.
    - (* CAS failed *)
      iApply (wp_cas_fail with "Hl"); eauto.
      { by right. }
      iDestruct "Hlog" as "[Hlog _]".
      iSpecialize ("Hlog" with "[]"); eauto.
  Qed.

  Lemma refines_faa_l K Γ E l e2 (i2 : Z) t A :
    IntoVal e2 #i2 →
    (|={⊤,E}=> ∃ (i1 : Z), ▷ l ↦ #i1 ∗
     ▷ (l ↦ #(i1 + i2) -∗ {E;Γ} ⊨ fill K (of_val #i1) << t : A))
    -∗ Γ ⊨ fill K (FAA #l e2) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (i1) "[Hl Hlog]". iModIntro.
    by iApply (wp_faa with "Hl").
  Qed.

End rules.
