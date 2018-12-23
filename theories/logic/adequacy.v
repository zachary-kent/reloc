(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Adequacy statements for the refinement proposition *)
From iris.algebra Require Import auth frac agree.
From iris.base_logic.lib Require Import auth.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Export adequacy.
From reloc.logic Require Export spec_ra model.

Class relocPreG Σ := RelocPreG {
  reloc_preG_heap :> heapPreG Σ;
  reloc_preG_cfg  :> inG Σ (authR cfgUR)
}.

Definition relocΣ : gFunctors := #[heapΣ; authΣ cfgUR].
Instance subG_relocPreG {Σ} : subG relocΣ Σ → relocPreG Σ.
Proof. solve_inG. Qed.

Definition pure_lty2 `{relocG Σ} (P : val → val → Prop) :=
  Lty2 (λ v v', ⌜P v v'⌝)%I.

Lemma refines_adequate Σ `{relocPreG Σ}
  (A : ∀ `{relocG Σ}, lty2)
  (P : val → val → Prop) e e' σ :
  (∀ `{relocG Σ}, ∀ v v', A v v' -∗ pure_lty2 P v v') →
  (∀ `{relocG Σ}, {⊤;∅} ⊨ e << e' : A) →
  adequate NotStuck e σ
    (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h)
            ∧ P v v').
Proof.
  intros HA Hlog.
  eapply (heap_adequacy Σ _); iIntros (Hinv).
  iMod (own_alloc (● (to_tpool [e'], to_gen_heap (heap σ))
    ⋅ ◯ ((to_tpool [e'] : tpoolUR, ∅) : cfgUR)))
    as (γc) "[Hcfg1 Hcfg2]".
  { apply auth_valid_discrete_2. split=>//.
    - apply prod_included. split=>///=.
      (* TODO: use gmap.empty_included *) eexists. by rewrite left_id.
    - split=>//. apply to_tpool_valid. apply to_gen_heap_valid. }
  set (Hcfg := RelocG _ _ (CFGSG _ _ γc)).
  iMod (inv_alloc specN _ (spec_inv ([e'], σ)) with "[Hcfg1]") as "#Hcfg".
  { iNext. iExists [e'], σ. eauto. }
  iApply wp_fupd. iApply wp_wand_r.
  iSplitL.
  - iPoseProof (Hlog _) as "Hrel".
    rewrite refines_eq /refines_def /spec_ctx.
    iSpecialize ("Hrel" $! ∅ with "Hcfg []").
    { iApply env_ltyped2_empty. }
    rewrite !fmap_empty !subst_map_empty.
    iApply fupd_wp.
    iApply ("Hrel" $! 0%nat []).
    rewrite tpool_mapsto_eq /tpool_mapsto_def. iFrame.
  - iIntros (v).
    iDestruct 1 as (v') "[Hj Hinterp]".
    rewrite HA.
    iDestruct "Hinterp" as %Hinterp.
    iInv specN as (tp σ') ">[Hown Hsteps]" "Hclose"; iDestruct "Hsteps" as %Hsteps'.
    rewrite tpool_mapsto_eq /tpool_mapsto_def /=.
    iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
    move: Hvalid=> /auth_valid_discrete_2
       [/prod_included [/tpool_singleton_included Hv2 _] _].
    destruct tp as [|? tp']; simplify_eq/=.
    iMod ("Hclose" with "[-]") as "_".
    { iExists (_ :: tp'), σ'. eauto. }
    iIntros "!> !%"; eauto.
Qed.

Theorem refines_typesafety Σ `{relocPreG Σ} e e' e1
        (A : ∀ `{relocG Σ}, lty2) thp σ σ' :
  (∀ `{relocG Σ}, {⊤;∅} ⊨ e << e' : A) →
  rtc erased_step ([e], σ) (thp, σ') → e1 ∈ thp →
  is_Some (to_val e1) ∨ reducible e1 σ'.
Proof.
  intros Hlog ??.
  cut (adequate NotStuck e σ (λ v _, ∃ thp' h v', rtc erased_step ([e'], σ) (of_val v' :: thp', h) ∧ True)); first (intros [_ ?]; eauto).
  eapply (refines_adequate _ A) ; eauto.
Qed.