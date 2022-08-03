(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Adequacy statements for the refinement proposition *)
From iris.algebra Require Import auth frac agree.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Export adequacy.
From reloc.logic Require Export spec_ra model.

Class relocPreG Σ := RelocPreG {
  reloc_preG_heap :> heapGpreS Σ;
  reloc_preG_cfg  :> inG Σ (authR cfgUR)
}.

Definition relocΣ : gFunctors := #[heapΣ; GFunctor (authR cfgUR)].
Global Instance subG_relocPreG {Σ} : subG relocΣ Σ → relocPreG Σ.
Proof. solve_inG. Qed.

Lemma refines_adequate Σ `{relocPreG Σ}
  (A : ∀ `{relocG Σ}, lrel Σ)
  (P : val → val → Prop) (e e' : expr) σ :
  (∀ `{relocG Σ}, ∀ v v', A v v' -∗ ⌜P v v'⌝) →
  (∀ `{relocG Σ}, ⊢ REL e << e' : A) →
  adequate NotStuck e σ
    (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h)
            ∧ P v v').
Proof.
  intros HA Hlog.
  eapply (heap_adequacy Σ _); iIntros (Hinv) "_".
  iMod (own_alloc (● (to_tpool [e'], to_heap (heap σ))
    ⋅ ◯ ((to_tpool [e'] : tpoolUR, ∅) : cfgUR)))
    as (γc) "[Hcfg1 Hcfg2]".
  { apply auth_both_valid_discrete. split=>//.
    - apply prod_included. split=>///=.
      apply: ucmra_unit_least.
    - split=>//. apply to_tpool_valid. apply to_heap_valid. }
  set (Hcfg := RelocG _ _ (CFGSG _ _ γc)).
  iMod (inv_alloc specN _ (spec_inv ([e'], σ)) with "[Hcfg1]") as "#Hcfg".
  { iNext. iExists [e'], σ. eauto. }
  iApply wp_fupd. iApply wp_wand_r.
  iSplitL.
  - iPoseProof (Hlog _) as "Hrel".
    rewrite refines_eq /refines_def /spec_ctx.
    iApply fupd_wp. iApply ("Hrel" $! (RefId 0 [])).
    iSplitR.
    + iExists _. by iFrame.
    + rewrite tpool_mapsto_eq /tpool_mapsto_def.
      by rewrite /to_tpool /= insert_empty map_fmap_singleton //.
  - iIntros (v).
    iDestruct 1 as (v') "[Hj Hinterp]".
    rewrite HA.
    iDestruct "Hinterp" as %Hinterp.
    iInv specN as (tp σ') ">[Hown Hsteps]" "Hclose"; iDestruct "Hsteps" as %Hsteps'.
    iDestruct "Hj" as "[#Hs Hj]".
    rewrite tpool_mapsto_eq /tpool_mapsto_def /=.
    iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
    move: Hvalid=> /auth_both_valid_discrete
       [/prod_included [/tpool_singleton_included Hv2 _] _].
    destruct tp as [|? tp']; simplify_eq/=.
    iMod ("Hclose" with "[-]") as "_".
    { iExists (_ :: tp'), σ'. eauto. }
    iIntros "!> !%"; eauto.
Qed.

Theorem refines_typesafety Σ `{relocPreG Σ} (e e' : expr) e1
        (A : ∀ `{relocG Σ}, lrel Σ) thp σ σ' :
  (∀ `{relocG Σ}, ⊢ REL e << e' : A) →
  rtc erased_step ([e], σ) (thp, σ') → e1 ∈ thp →
  not_stuck e1 σ'.
Proof.
  intros Hlog ??.
  cut (adequate NotStuck e σ (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h) ∧ True)); first (intros [_ ?]; eauto).
  eapply (refines_adequate _ A) ; eauto.
Qed.
