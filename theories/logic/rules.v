(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Core ReLoC rules *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Import proofmode.
From reloc.logic Require Import model proofmode.spec_tactics.
From reloc.prelude Require Import ctx_subst.

Local Set Default Proof Using "Type".

Section rules.
  Context `{relocG Σ}.
  Implicit Types A : lrel Σ.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Local Existing Instance pure_exec_fill.

  (** * Primitive rules *)

  (** ([fupd_refines] is defined in [logrel_binary.v]) *)

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
    iIntros "IH" ; iIntros (j) "Hs".
    iModIntro. wp_pures.
    iApply fupd_wp. iApply ("IH" with "Hs").
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
    iIntros "IH" ; iIntros (j) "Hs /=".
    iMod ("IH" with "Hs") as "IH".
    iModIntro. by wp_pures.
  Qed.

  Lemma refines_wp_l K e1 t A :
    (WP e1 {{ v,
        REL fill K (of_val v) << t : A }})%I -∗
    REL fill K e1 << t : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He".
    iIntros (j) "Hs /=".
    iModIntro. iApply wp_bind.
    iApply (wp_wand with "He").
    iIntros (v) "Hv".
    by iMod ("Hv" with "Hs").
  Qed.

  Lemma refines_atomic_l (E : coPset) K e1 t A
        (Hatomic : Atomic WeaklyAtomic e1) :
   (|={⊤,E}=> WP e1 @ E {{ v,
     REL fill K (of_val v) << t @ E : A }})%I -∗
   REL fill K e1 << t : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "Hlog".
    iIntros (j) "Hs /=". iModIntro.
    iApply wp_bind. iApply wp_atomic; auto.
    iMod "Hlog" as "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "Hlog".
    by iApply ("Hlog" with "Hs").
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
    iIntros "Hlog". iIntros (j) "Hj /=".
    tp_pures j ; auto.
    iApply ("Hlog" with "Hj").
  Qed.

  Lemma refines_right_bind k K e :
    refines_right k (fill K e) ≡ refines_right (RefId (tp_id k) (K ++ tp_ctx k)) e.
  Proof. rewrite /refines_right /=. by rewrite fill_app. Qed.

  Lemma refines_right_bind' j K K' e :
    refines_right (RefId j K) (fill K' e) ≡ refines_right (RefId j (K' ++ K)) e.
  Proof. rewrite /refines_right /=. by rewrite fill_app. Qed.

  (* A helper lemma for proving the stateful reductions for the RHS below *)
  Lemma refines_step_r E K' e1 e2 A :
    (∀ k, refines_right k e2 ={E}=∗
         ∃ v, refines_right k (of_val v) ∗ REL e1 << fill K' (of_val v) @ E : A) -∗
    REL e1 << fill K' e2 @ E : A.
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "He".
    iIntros (j) "Hs /=".
    rewrite refines_right_bind /=.
    iMod ("He" with "Hs") as (v) "[Hs He]".
    rewrite -refines_right_bind'.
    iSpecialize ("He" with "Hs").
    by iApply "He".
  Qed.

  Lemma refines_newproph_r E K t A
    (Hmasked : nclose specN ⊆ E) :
    (∀ (p : proph_id), REL t << fill K (of_val #p) @ E : A)%I
    ⊢ REL t << fill K NewProph @ E : A.
  Proof.
    iIntros "Hlog".
    iApply refines_step_r.
    iIntros (k) "[Hs Hj]".
    iMod (step_newproph with "[$Hs $Hj]") as (p) "Hj". done.
    iModIntro. iExists _. iFrame "Hj". by iApply "Hlog".
  Qed.

  Lemma refines_resolveproph_r E K t (p : proph_id) w A
    (Hmasked : nclose specN ⊆ E) :
    (REL t << fill K (of_val #()) @ E : A)%I
    ⊢ REL t << fill K (ResolveProph #p (of_val w)) @ E : A.
  Proof.
    iIntros "Hlog".
    iApply refines_step_r.
    iIntros (k) "[Hs Hj]".
    iMod (step_resolveproph with "[$Hs $Hj]") as "Hj". done.
    iModIntro. iExists _. iFrame "Hj". by iApply "Hlog".
  Qed.

  Lemma refines_store_r E K l e e' v v' A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e' v' →
    l ↦ₛ v ⊢
    (l ↦ₛ v' -∗ REL e << fill K (of_val #()) @ E : A) -∗
    REL e << fill K (#l <- e') @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk". simpl.
    tp_store k. iModIntro. iExists _. iFrame.
    by iApply "Hlog".
  Qed.

  Lemma refines_alloc_r E K e v t A
    (Hmasked : nclose specN ⊆ E) :
    IntoVal e v →
    (∀ l : loc, l ↦ₛ v -∗ REL t << fill K (of_val #l) @ E : A)%I
    ⊢ REL t << fill K (ref e) @ E : A.
  Proof.
    rewrite /IntoVal. intros <-.
    iIntros "Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_alloc k as l "Hl".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_load_r E K l q v t A
    (Hmasked : nclose specN ⊆ E) :
    l ↦ₛ{q} v ⊢
    (l ↦ₛ{q} v -∗ REL t << fill K (of_val v) @ E : A)
    -∗ REL t << (fill K !#l) @ E : A.
  Proof.
    iIntros "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_load k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_xchg_r E K l e1 v1 v t A :
    nclose specN ⊆ E →
    IntoVal e1 v1 →
    l ↦ₛ v ⊢
    (l ↦ₛ v1 -∗ REL t << fill K (of_val v) @ E : A)
    -∗ REL t << fill K (Xchg #l e1) @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (?<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    admit.
  Admitted.


  Lemma refines_cmpxchg_fail_r E K l e1 e2 v1 v2 v t A :
    nclose specN ⊆ E →
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    vals_compare_safe v v1 →
    v ≠ v1 →
    l ↦ₛ v ⊢
    (l ↦ₛ v -∗ REL t << fill K (of_val (v, #false)) @ E : A)
    -∗ REL t << fill K (CmpXchg #l e1 e2) @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (?<-<-??) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_cmpxchg_fail k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_cmpxchg_suc_r E K l e1 e2 v1 v2 v t A :
    nclose specN ⊆ E →
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    vals_compare_safe v v1 →
    v = v1 →
    l ↦ₛ v ⊢
    (l ↦ₛ v2 -∗ REL t << fill K (of_val (v, #true)) @ E : A)
    -∗ REL t << fill K (CmpXchg #l e1 e2) @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (?<-<-??) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_cmpxchg_suc k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_faa_r E K l e2 (i1 i2 : Z) t A :
    nclose specN ⊆ E →
    IntoVal e2 #i2 →
    l ↦ₛ #i1 -∗
    (l ↦ₛ #(i1+i2) -∗ REL t << fill K (of_val #i1) @ E : A)
    -∗ REL t << fill K (FAA #l e2) @ E : A.
  Proof.
    rewrite /IntoVal. iIntros (?<-) "Hl Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_faa k.
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  Lemma refines_fork_r E K (e t : expr) A
   (Hmasked : nclose specN ⊆ E) :
   (∀ k, refines_right k e -∗
     REL t << fill K (of_val #()) @ E : A) ⊢
   REL t << fill K (Fork e) @ E : A.
  Proof.
    iIntros "Hlog".
    iApply refines_step_r.
    iIntros (k) "Hk".
    tp_fork k as k' "Hk'".
    iModIntro. iExists _. iFrame. by iApply "Hlog".
  Qed.

  (** ** Primitive structural rules *)
  Lemma refines_fork e e' :
    (REL e << e' : ()%lrel) -∗
    REL Fork e << Fork e' : ().
  Proof.
    rewrite refines_eq /refines_def.
    iIntros "H".
    iIntros (j) "Hs /=".
    tp_fork j as k' "Hk'". iModIntro.
    simpl.
    iSpecialize ("H" with "Hk'").
    iApply (wp_fork with "[H]").
    - iNext. iMod "H". iApply (wp_wand with "H"). eauto.
    - iNext. iExists _. rewrite /refines_right.
      eauto with iFrame.
  Qed.

  (** This rule is useful for proving that functions refine each other *)
  Lemma refines_arrow_val (v v' : val) A A' :
    □(∀ v1 v2, A v1 v2 -∗
      REL App v (of_val v1) << App v' (of_val v2) : A') -∗
    REL (of_val v) << (of_val v') : (A → A')%lrel.
  Proof.
    iIntros "#H".
    iApply refines_ret. iModIntro.
    iModIntro. iIntros (v1 v2) "HA".
    iSpecialize ("H" with "HA").
    by iApply "H".
  Qed.

  (** * Some derived (symbolic execution) rules *)

  (** ** Stateful reductions on the LHS *)

  Lemma refines_fork_l K E e t A :
   (|={⊤,E}=> ▷ (WP e {{ _, True }} ∗
    (REL fill K (of_val #()) << t @ E : A))) ⊢
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
    ⊢ REL fill K (ref e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog". iModIntro.
    iApply (wp_alloc _ _ v with "[//]"). iIntros "!>" (l) "[? _]". by iApply "Hlog".
  Qed.

  Lemma refines_newproph_l K E t A :
    (|={⊤,E}=> ▷ (∀ (vs : list (val*val)) (p : proph_id),
           proph p vs -∗
           REL fill K (of_val #p) << t @ E : A))%I
    ⊢ REL fill K NewProph << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog". iModIntro.
    iApply wp_new_proph=>//.
  Qed.

  Lemma refines_resolveproph_l K E (p : proph_id) w t A :
    (|={⊤,E}=> ∃ vs,
           ▷ (proph p vs) ∗
           ▷ (∀ (vs' : list (val*val)), ⌜vs = (LitV LitUnit,w)::vs'⌝ -∗
                  proph p vs' -∗
                  REL fill K (of_val #()) << t @ E : A))%I
    ⊢ REL fill K (ResolveProph #p w) << t : A.
  Proof.
    iIntros "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (vs) "[>Hp Hlog]". iModIntro.
    iApply (wp_resolve_proph with "Hp") =>//.
    iNext. iIntros (vs'). by rewrite -bi.wand_curry.
  Qed.

  Lemma refines_resolveatomic_l K E (p : proph_id) e w t A :
    Atomic StronglyAtomic e →
    to_val e = None →
    (|={⊤,E}=> ∃ vs,
           ▷ (proph p vs) ∗
           WP e @ E {{ v, ∀ (vs' : list (val*val)), ⌜vs = (v,w)::vs'⌝ -∗
                  proph p vs' -∗
                  REL fill K (of_val v) << t @ E : A }})%I
    ⊢ REL fill K (Resolve e #p w) << t : A.
  Proof.
    iIntros (??) "Hlog".
    iApply refines_atomic_l; auto.
    { apply strongly_atomic_atomic. apply _. }
    iMod "Hlog" as (vs) "[>Hp Hlog]". iModIntro.
    iApply (wp_resolve with "Hp"); auto.
  Qed.

  Lemma refines_load_l K E l q t A :
    (|={⊤,E}=> ∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (REL fill K (of_val v') << t @ E : A)))%I
    ⊢ REL fill K (! #l) << t : A.
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
    ⊢ REL fill K (#l <- e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v) "[Hl Hlog]". iModIntro.
    iApply (wp_store _ _ _ _ v' with "Hl"); auto.
  Qed.

  Lemma refines_xchg_l K E l e v' t A :
    IntoVal e v' →
    (|={⊤,E}=> ∃ v, ▷ l ↦ v ∗
      ▷(l ↦ v' -∗ REL fill K (of_val v) << t @ E : A))
    ⊢ REL fill K (Xchg #l e) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v) "[Hl Hlog]". iModIntro.
    iApply (wp_xchg _ _ _ _ v' with "Hl"); auto.
  Qed.

  Lemma refines_cmpxchg_l K E l e1 e2 v1 v2 t A :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    val_is_unboxed v1 →
    (|={⊤,E}=> ∃ v', ▷ l ↦ v' ∗
     (⌜v' ≠ v1⌝ -∗ ▷ (l ↦ v' -∗ REL fill K (of_val (v', #false)) << t @ E : A)) ∧
     (⌜v' = v1⌝ -∗ ▷ (l ↦ v2 -∗ REL fill K (of_val (v', #true)) << t @ E : A)))
    ⊢ REL fill K (CmpXchg #l e1 e2) << t : A.
  Proof.
    iIntros (<-<-?) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (v') "[Hl Hlog]". iModIntro.
    destruct (decide (v' = v1)).
    - (* CmpXchg successful *) subst.
      iApply (wp_cmpxchg_suc with "Hl"); eauto.
      { by right. }
      iDestruct "Hlog" as "[_ Hlog]".
      iSpecialize ("Hlog" with "[]"); eauto.
    - (* CmpXchg failed *)
      iApply (wp_cmpxchg_fail with "Hl"); eauto.
      { by right. }
      iDestruct "Hlog" as "[Hlog _]".
      iSpecialize ("Hlog" with "[]"); eauto.
  Qed.

  Lemma refines_faa_l K E l e2 (i2 : Z) t A :
    IntoVal e2 #i2 →
    (|={⊤,E}=> ∃ (i1 : Z), ▷ l ↦ #i1 ∗
     ▷ (l ↦ #(i1 + i2) -∗ REL fill K (of_val #i1) << t @ E : A))
    ⊢ REL fill K (FAA #l e2) << t : A.
  Proof.
    iIntros (<-) "Hlog".
    iApply refines_atomic_l; auto.
    iMod "Hlog" as (i1) "[Hl Hlog]". iModIntro.
    by iApply (wp_faa with "Hl").
  Qed.

End rules.
