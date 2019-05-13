(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Core ReLoC rules *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import list.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Import proofmode.
From reloc.logic Require Import model proofmode.spec_tactics.
From reloc.prelude Require Import ctx_subst.

Section rules.
  Context `{relocG Σ}.
  Implicit Types A : lrel Σ.
  Implicit Types e t : expr.
  Implicit Types v w : val.

  (** * Primitive rules *)

  (** ([fupd_logrel] is defined in [logrel_binary.v]) *)

  (** ** Forward reductions on the LHS *)

  Lemma refines_pure_l n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    ▷^n (REL fill K' e' << t : A)
    ⊢ REL fill K' e << t : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (ρ) "#Hs"; iIntros (j K) "Hj /=".
    iModIntro. wp_pures.
    iApply fupd_wp. iApply ("IH" with "Hs Hj").
  Qed.

  Lemma refines_masked_l E n
    (K' : list ectx_item) e e' t A ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL fill K' e' << t @ E : A)
    ⊢ REL fill K' e << t @ E : A.
  Proof.
    intros Hpure Hϕ.
    rewrite refines_eq /refines_def.
    iIntros "IH" (ρ) "#Hs"; iIntros (j K) "Hj /=".
    iMod ("IH" with "Hs Hj") as "IH".
    iModIntro. by wp_pures.
  Qed.

  Lemma refines_wp_l K e1 e2 A :
    (WP e1 {{ v,
        REL fill K (of_val v) << e2 : A }})%I -∗
    REL fill K e1 << e2 : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He".
    iIntros (ρ) "#Hs". iIntros (j K') "Hj /=".
    iModIntro. iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    by iMod ("Hv" with "Hs Hj").
  Qed.

  Lemma refines_atomic_l (E : coPset) K e1 e2 A
        (Hatomic : Atomic WeaklyAtomic e1) :
   (|={⊤,E}=> WP e1 @ E {{ v,
     REL fill K (of_val v) << e2 @ E : A }})%I -∗
   REL fill K e1 << e2 : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hlog".
    iIntros (ρ) "#Hs". iIntros (j K') "Hj /=". iModIntro.
    iApply wp_bind. iApply wp_atomic; auto.
    iMod "Hlog" as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    by iApply ("Hlog" with "Hs Hj").
  Qed.

  (** ** Forward reductions on the RHS *)

  Lemma refines_pure_r E K' e e' t A n
    (Hspec : nclose specN ⊆ E) ϕ :
    PureExec ϕ n e e' →
    ϕ →
    (REL t << fill K' e' @ E : A)
    ⊢ REL t << fill K' e @ E : A.
  Proof.
    rewrite refines_eq /refines_def => Hpure Hϕ.
    iIntros "Hlog". iIntros (ρ) "#Hs". iIntros (j K) "Hj /=".
    tp_pure j _; auto.
    iApply ("Hlog" with "Hs Hj").
  Qed.

  (* A helper lemma for proving the stateful reductions for the RHS below *)
  Lemma refines_step_r Φ E K' e1 e2 A :
    (∀ ρ j K, spec_ctx ρ -∗ (j ⤇ fill K e2 ={E}=∗ ∃ v, j ⤇ fill K (of_val v)
                  ∗ Φ v)) -∗
    (∀ v, Φ v -∗ REL e1 << fill K' (of_val v) @ E : A) -∗
    REL e1 << fill K' e2 @ E : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He Hlog".
    iIntros (ρ) "#Hs". iIntros (j K) "Hj /=".
    rewrite -fill_app.
    iMod ("He" $! ρ j with "Hs Hj") as (v) "[Hj Hv]".
    iSpecialize ("Hlog" $! v with "Hv Hs").
    rewrite fill_app.
    by iApply "Hlog".
  Qed.

  Lemma refines_newproph_r E K t A
    (Hmasked : nclose specN ⊆ E) :
    (∀ (p : proph_id), REL t << fill K (of_val #p) @ E : A)%I
    -∗ REL t << fill K NewProph @ E : A.
  Proof.
    iIntros "Hlog".
    pose (Φ := (fun w => ∃ (p : proph_id), ⌜w = (# p)⌝ : iProp Σ)%I).
    iApply (refines_step_r Φ); simpl; auto.
    { cbv[Φ].
      iIntros (ρ j K') "#Hs Hj /=".
      iMod (step_newproph with "[$Hs $Hj]") as (p) "Hj". done.
      iModIntro. iExists _. iFrame. iExists _. iFrame. eauto. }
    iIntros (v') "He'". iDestruct "He'" as (p) "%". subst.
    by iApply "Hlog".
  Qed.

  Lemma refines_resolveproph_r E K t (p : proph_id) w A
    (Hmasked : nclose specN ⊆ E) :
    (REL t << fill K (of_val #()) @ E : A)%I
    -∗ REL t << fill K (ResolveProph #p (of_val w)) @ E : A.
  Proof.
    iIntros "Hlog".
    pose (Φ := (fun w => ⌜w = #()⌝ : iProp Σ)%I).
    iApply (refines_step_r Φ); simpl; auto.
    { cbv[Φ].
      iIntros (ρ j K') "#Hs Hj /=".
      iMod (step_resolveproph with "[$Hs $Hj]") as "Hj". done.
      iModIntro. iExists _. iFrame. eauto. }
    iIntros (v') "He'". iDestruct "He'" as %->.
    by iApply "Hlog".
  Qed.

  Lemma refines_alloc_r E K e v t A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e v →
    (∀ l : loc, l ↦ₛ v -∗ REL t << fill K (of_val #l) @ E : A)%I
    -∗ REL t << fill K (ref e) @ E : A.
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

  Lemma refines_load_r E K l q v t A
    (Hmasked : nclose specN ⊆ E) :
    l ↦ₛ{q} v -∗
    (l ↦ₛ{q} v -∗ REL t << fill K (of_val v) @ E : A)
    -∗ REL t << (fill K !#l) @ E : A.
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

  Lemma refines_store_r E K l e e' v v' A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e' v' →
    l ↦ₛ v -∗
    (l ↦ₛ v' -∗ REL e << fill K (of_val #()) @ E : A) -∗
    REL e << fill K (#l <- e') @ E : A.
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

  Lemma refines_cas_fail_r E K l e1 e2 v1 v2 v t A :
    nclose specN ⊆ E →
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    vals_cas_compare_safe v v1 →
    v ≠ v1 →
    l ↦ₛ v -∗
    (l ↦ₛ v -∗ REL t << fill K (of_val #false) @ E : A)
    -∗ REL t << fill K (CAS #l e1 e2) @ E : A.
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

  Lemma refines_cas_suc_r E K l e1 e2 v1 v2 v t A :
    nclose specN ⊆ E →
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    val_is_unboxed v1 →
    v = v1 →
    l ↦ₛ v -∗
    (l ↦ₛ v2 -∗ REL t << fill K (of_val #true) @ E : A)
    -∗ REL t << fill K (CAS #l e1 e2) @ E : A.
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

  Lemma refines_faa_r E K l e2 (i1 i2 : Z) t A :
    nclose specN ⊆ E →
    IntoVal e2 #i2 →
    l ↦ₛ #i1 -∗
    (l ↦ₛ #(i1+i2) -∗ REL t << fill K (of_val #i1) @ E : A)
    -∗ REL t << fill K (FAA #l e2) @ E : A.
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

  Lemma refines_fork_r E K (e t : expr) A
   (Hmasked : nclose specN ⊆ E) :
   (∀ i, i ⤇ e -∗
     REL t << fill K (of_val #()) @ E : A) -∗
   REL t << fill K (Fork e) @ E : A.
  Proof.
    iIntros "Hlog".
    pose (Φ := (fun (v : val) => ∃ i, i ⤇ e ∗ ⌜v = #()⌝%V)%I).
    iApply (refines_step_r Φ with "[]"); cbv[Φ].
    { iIntros (ρ j K') "#Hspec Hj".
      tp_fork j as i "Hi".
      iModIntro. iExists #(). iFrame. eauto.
    }
    iIntros (v). iDestruct 1 as (i) "[Hi %]"; subst.
    by iApply "Hlog".
  Qed.

  (** ** Primitive structural rules *)
  Lemma refines_fork e e' :
    (REL e << e' : ()%lrel) -∗
    REL Fork e << Fork e' : ().
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "H".
    iIntros (ρ) "#Hs"; iIntros (j K) "Hj /=".
    tp_fork j as i "Hi". iModIntro.
    iSpecialize ("H" with "Hs").
    iSpecialize ("H" $! i [] with "Hi"). simpl.
    iApply (wp_fork with "[H]").
    - iNext. iMod "H". iApply (wp_wand with "H"). eauto.
    - iNext. iExists _. by iFrame.
  Qed.

  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val v v' (f x f' x' : binder) eb eb' A A' :
    AsRecV v f x eb →
    AsRecV v' f' x' eb' →
    □(∀ v1 v2, A v1 v2 -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') -∗
    REL v << v' : (A → A')%lrel.
  Proof.
    rewrite /AsRecV. iIntros (-> ->) "#H".
    iApply refines_spec_ctx. iDestruct 1 as (ρ) "#Hs".
    iApply refines_ret. iModIntro.
    iModIntro. iIntros (v1 v2) "HA".
    iSpecialize ("H" with "HA").
    rewrite refines_eq /refines_def.
    by iApply "H".
  Qed.

  (** * Some derived (symbolic execution) rules *)

  (** ** Stateful reductions on the LHS *)

  Lemma refines_fork_l K E e t A :
   (|={⊤,E}=> ▷ (WP e {{ _, True }} ∗
    (REL fill K (of_val #()) << t @ E : A))) -∗
   REL fill K (Fork e) << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as "[Hsafe Hlog]". iModIntro.
    iApply (wp_fork with "Hsafe"). eauto.
  Qed.

  Lemma refines_alloc_l K E e v t A :
    IntoVal e v →
    (|={⊤,E}=> ▷ (∀ l : loc, l ↦ v -∗
           REL fill K (of_val #l) << t @ E : A))%I
    -∗ REL fill K (ref e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog". iModIntro.
    iApply (wp_alloc _ _ v); auto.
  Qed.

  Lemma refines_newproph_l K E t A :
    (|={⊤,E}=> ▷ (∀ (vs : list val) (p : proph_id),
           proph p vs -∗
           REL fill K (of_val #p) << t @ E : A))%I
    -∗ REL fill K NewProph << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog". iModIntro.
    iApply wp_new_proph=>//.
  Qed.

  Lemma refines_resolveproph_l K E (p : proph_id) w t A :
    (|={⊤,E}=> ∃ vs,
           ▷ (proph p vs) ∗
           ▷ (∀ (vs' : list val), ⌜vs = w::vs'⌝ -∗
                  proph p vs' -∗
                  REL fill K (of_val #()) << t @ E : A))%I
    -∗ REL fill K (ResolveProph #p w) << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (vs) "[>Hp Hlog]". iModIntro.
    iApply (wp_resolve_proph with "Hp") =>//.
    iNext. iIntros (vs'). by rewrite -bi.wand_curry.
  Qed.

  Lemma refines_load_l K E l q t A :
    (|={⊤,E}=> ∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (REL fill K (of_val v') << t @ E : A)))%I
    -∗ REL fill K (! #l) << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v') "[Hl Hlog]". iModIntro.
    iApply (wp_load with "Hl"); auto.
  Qed.

  Lemma refines_store_l K E l e v' t A :
    IntoVal e v' →
    (|={⊤,E}=> ∃ v, ▷ l ↦ v ∗
      ▷(l ↦ v' -∗ REL fill K (of_val #()) << t @ E : A))
    -∗ REL fill K (#l <- e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v) "[Hl Hlog]". iModIntro.
    iApply (wp_store _ _ _ _ v' with "Hl"); auto.
  Qed.

  Lemma refines_cas_l K E l e1 e2 v1 v2 t A :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    val_is_unboxed v1 →
    (|={⊤,E}=> ∃ v', ▷ l ↦ v' ∗
     (⌜v' ≠ v1⌝ -∗ ▷ (l ↦ v' -∗ REL fill K (of_val #false) << t @ E : A)) ∧
     (⌜v' = v1⌝ -∗ ▷ (l ↦ v2 -∗ REL fill K (of_val #true) << t @ E : A)))
    -∗ REL fill K (CAS #l e1 e2) << t : A.
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

  Lemma refines_faa_l K E l e2 (i2 : Z) t A :
    IntoVal e2 #i2 →
    (|={⊤,E}=> ∃ (i1 : Z), ▷ l ↦ #i1 ∗
     ▷ (l ↦ #(i1 + i2) -∗ REL fill K (of_val #i1) << t @ E : A))
    -∗ REL fill K (FAA #l e2) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (i1) "[Hl Hlog]". iModIntro.
    by iApply (wp_faa with "Hl").
  Qed.

End rules.
