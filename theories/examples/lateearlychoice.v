From iris.heap_lang Require Import lifting.
From reloc Require Import reloc.

Definition rand: val :=
  λ: "_",
    let: "y" := ref #false in
    Fork ("y" <- #true) ;;
    !"y".

Definition earlyChoice: val :=
  λ: "x",
    let: "r" := rand #() in
    "x" <- #0 ;;
    "r".

Definition lateChoice': val :=
  λ: "x",
    let: "p" := NewProph in
    "x" <- #0 ;;
    let: "r" := rand #() in
    resolve_proph: "p" to: "r" ;;
    "r".

Definition lateChoice: val :=
  λ: "x",
    "x" <- #0 ;;
    let: "r" := rand #() in
    "r".

Section proof.
  Context `{relocG Σ}.

  Lemma refines_rand_r (b : bool) E K e A :
    nclose relocN ⊆ E →
    (REL e << fill K (of_val #b) @ E : A) -∗
    REL e << fill K (rand #()) @ E : A.
  Proof.
    iIntros (?) "He".
    rel_rec_r. rel_alloc_r y as "Hy".
    repeat rel_pure_r. rel_fork_r i as "Hi".
    repeat rel_pure_r.
    iApply refines_spec_ctx. iDestruct 1 as (ρ) "#Hρ".
    destruct b.
    - tp_store i. rel_load_r. iApply "He".
    - rel_load_r. iApply "He".
  Qed.

  Lemma refines_rand_l K t A :
    ▷ (∀ (b: bool), REL fill K (of_val #b) << t : A) -∗
    REL fill K (rand #()) << t : A.
  Proof.
    iIntros "He".
    rel_rec_l. rel_alloc_l y as "Hy".
    iMod (inv_alloc (nroot.@"randN") _ (∃ (b: bool), y ↦ #b)%I with "[Hy]") as "#Hinv"; first by eauto.
    repeat rel_pure_l. rel_fork_l. iModIntro.
    iSplitR.
    - iNext. iInv (nroot.@"randN") as (b) "Hy" "Hcl"; wp_store;
        iMod ("Hcl" with "[Hy]") as "_"; eauto with iFrame.
    - iNext. repeat rel_pure_l.
      rel_load_l_atomic.
      iInv (nroot.@"randN") as (b) "Hy" "Hcl".
      iModIntro. iExists _; iFrame. iNext. iIntros "Hy".
      iMod ("Hcl" with "[Hy]") as "_"; eauto with iFrame.
  Qed.

  Definition val_to_bool (vs : list val) : bool :=
    match vs with
    | LitV (LitBool b)::_ => b
    | _                   => true
    end.

  Lemma late'_early_choice :
    REL lateChoice' << earlyChoice : ref lrel_int → lrel_bool.
  Proof.
    unfold lateChoice', earlyChoice.
    iApply refines_arrow_val.
    iModIntro. iIntros (x x') "#Hxx".
    rel_rec_l. rel_rec_r.
    rel_newproph_l vs p as "Hp".
    repeat rel_pure_l.
    rel_apply_r (refines_rand_r (val_to_bool vs)).
    repeat rel_pure_r.
    iApply (refines_seq lrel_unit).
    { iApply refines_store.
      - iApply refines_ret. iApply "Hxx".
      - rel_values. }
    rel_apply_l refines_rand_l.
    iNext. iIntros (b). repeat rel_pure_l.
    rel_apply_l refines_resolveproph_l. iModIntro.
    iExists _; iFrame. iNext. iIntros (vs' ->) "H".
    repeat rel_pure_l. rel_values.
  Qed.

  Lemma early_late_choice :
    REL earlyChoice << lateChoice : ref lrel_int → lrel_bool.
  Proof.
    unfold lateChoice, earlyChoice.
    iApply refines_arrow_val.
    iModIntro. iIntros (x x') "#Hxx".
    rel_rec_l. rel_rec_r.
    rel_apply_l refines_rand_l.
    iNext. iIntros (b). repeat rel_pure_l.
    iApply (refines_seq lrel_unit).
    { iApply refines_store.
      - iApply refines_ret. iApply "Hxx".
      - rel_values. }
    rel_apply_r (refines_rand_r b).
    repeat rel_pure_r. rel_values.
  Qed.

  Lemma late_late'_choice :
    REL lateChoice << lateChoice' : ref lrel_int → lrel_bool.
  Proof.
    unfold lateChoice, lateChoice'.
    iApply refines_arrow_val.
    iModIntro. iIntros (x x') "#Hxx".
    rel_rec_l. rel_rec_r.
    rel_newproph_r p. repeat rel_pure_r.
    iApply (refines_seq lrel_unit with "[Hxx]").
    { iApply refines_store.
      - iApply refines_ret. iApply "Hxx".
      - rel_values. }
    rel_apply_l refines_rand_l.
    iNext. iIntros (b). repeat rel_pure_l.
    rel_apply_r (refines_rand_r b).
    repeat rel_pure_r.
    rel_apply_r refines_resolveproph_r.
    repeat rel_pure_r. rel_values.
  Qed.

End proof.

Theorem late_early_ctx_refinement :
  ∅ ⊨ lateChoice ≤ctx≤ earlyChoice : ref TNat → TBool.
Proof.
  eapply (ctx_refines_transitive ∅ (ref TNat → TBool)).
  - eapply (refines_sound relocΣ).
    iIntros (? Δ). iApply late_late'_choice.
  - eapply (refines_sound relocΣ).
    iIntros (? Δ). iApply late'_early_choice.
Qed.

Theorem early_late_ctx_refinement :
  ∅ ⊨ earlyChoice ≤ctx≤ lateChoice : ref TNat → TBool.
Proof.
  eapply (refines_sound relocΣ).
  iIntros (? Δ). iApply early_late_choice.
Qed.
