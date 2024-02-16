From iris.heap_lang Require Import derived_laws.
From reloc Require Import reloc lib.lock.

(* for rand (), val_to_bool *)
From reloc.examples Require Import lateearlychoice.

Definition newcoin : val := λ: <>, ref #false.
Definition flip : val := λ: "c", "c" <- rand #().
Definition read : val := λ: "c", !"c".

Definition newcoin_lazy : val := λ: <>, ref (SOME #false).

Definition flip_lazy : val := λ: "c",
  "c" <- NONE.
Definition flip_lazy' : val := λ: "c" "lk" "p",
  acquire "lk";;
  "c" <- NONE;;
  release "lk".

Definition read_lazy : val := rec: "read" "c" :=
  match: !"c" with
    SOME "v" => "v"
  | NONE  =>
      let: "x" := rand #() in
      if: CAS "c" NONEV (SOME "x")
      then "x"
      else "read" "c"
  end.
Definition read_lazy' : val := λ: "c" "lk" "p",
  acquire "lk";;
  let: "r" :=
    match: !"c" with
      InjR "v" => "v"
    | InjL <>  =>
      let: "x" := rand #() in
      "c" <- SOME "x";;
      resolve_proph: "p" to: "x";;
      "x"
    end in
  release "lk";;
  "r".

Definition coin1 : expr :=
  let: "c" := newcoin #() in
  ((λ: <>, read "c"), (λ: <>, flip "c")).
Definition coin2 : expr :=
  let: "c" := newcoin_lazy #() in
  ((λ: <>, read_lazy "c"), (λ: <>, flip_lazy "c")).
Definition coin2' : expr :=
  let: "c" := newcoin_lazy #() in
  let: "p" := NewProph in
  let: "lk" := newlock #() in
  ((λ: <>, read_lazy' "c" "lk" "p"), (λ: <>, flip_lazy' "c" "lk" "p")).

Section proofs.
  Context `{!relocG Σ, !lockG Σ}.

  Definition coinN := nroot.@"coins".

  (** Lazy coin (with prophecies) refines eager coin *)
  Definition I (cl ce : loc) (p : proph_id) :=
    (∃ vs : list (val*val), proph p vs ∗
    (cl ↦ NONEV ∗ ce ↦ₛ #(extract_bool vs)
    ∨ ∃ (b:bool), cl ↦ SOMEV #b ∗ ce ↦ₛ #b))%I.

  Lemma coin_lazy'_eager_refinement :
    ⊢ REL coin2' << coin1 : (() → lrel_bool) * (() → ()).
  Proof.
    unfold coin1, coin2'.
    rel_rec_r. rel_alloc_r ce as "Hce". do 2 rel_pure_r.

    rel_rec_l. rel_pure_l. rel_alloc_l cl as "Hcl".
    do 2 rel_pure_l. rel_newproph_l vs p as "Hp".
    do 2 rel_pure_l.
    rel_apply_l (refines_newlock_l coinN (I cl ce p) with "[-]").
    { iExists vs. iFrame. iRight. iExists false. iFrame. }
    clear vs.
    iNext. iIntros (lk γ) "#Hlk /=". do 2 rel_pure_l.
    iApply refines_pair.
    - rel_pure_l; rel_pure_r. iApply refines_arrow. iIntros (??) "!> _".
      rel_pure_l; rel_rec_l; rel_pure_r; rel_rec_r. repeat rel_pure_l.
      rel_apply_l (refines_acquire_l with "Hlk").
      iNext. iIntros "Hlocked".
      iDestruct 1 as (vs) "[Hp H]". repeat rel_pure_l.
      iDestruct "H" as "[[Hcl Hce]|H]"; last iDestruct "H" as (x) "[Hcl Hce]";
        rel_load_l; rel_load_r; repeat rel_pure_l.
      + rel_apply_l refines_rand_l. iNext. iIntros (b).
        repeat rel_pure_l. rel_store_l. repeat rel_pure_l.
        rel_apply_l refines_resolveproph_l. iModIntro. iExists _; iFrame.
        iNext. iIntros (vs' ->) "Hp". iSimpl in "Hce". repeat rel_pure_l.
        rel_apply_l (refines_release_l with "Hlk Hlocked [-]").
        { iExists vs'. iFrame. iRight. iExists b. iFrame. }
        iNext. repeat rel_pure_l; rel_values.
      + rel_apply_l (refines_release_l with "Hlk Hlocked [-]").
        { iExists vs. iFrame. iRight. iExists x. iFrame. }
        iNext. repeat rel_pure_l; rel_values.
    - rel_pure_l; rel_pure_r. iApply refines_arrow. iIntros (??) "!> _".
      rel_pure_l; rel_rec_l; rel_pure_r; rel_rec_r. repeat rel_pure_l.
      rel_apply_l (refines_acquire_l with "Hlk").
      iNext. iIntros "Hlocked".
      iDestruct 1 as (vs) "[Hp H]". repeat rel_pure_l.
      iDestruct "H" as "[[Hcl Hce]|H]"; last iDestruct "H" as (x) "[Hcl Hce]";
        rel_store_l; repeat rel_pure_l.
      + rel_apply_r (refines_rand_r (extract_bool vs)).
        rel_store_r.
        rel_apply_l (refines_release_l with "Hlk Hlocked [$]").
        iNext. rel_values.
      + rel_apply_r (refines_rand_r (extract_bool vs)).
        rel_store_r.
        rel_apply_l (refines_release_l with "Hlk Hlocked [$]").
        iNext. rel_values.
  Qed.

  (** Eager coin refines lazy coin (with prophecies).
      This part is easier. *)
  Lemma coin_eager_lazy'_refinement :
    ⊢ REL coin1 << coin2' : (() → lrel_bool) * (() → ()).
  Proof.
    unfold coin1, coin2'.
    rel_rec_l. rel_alloc_l ce as "Hce". do 2 rel_pure_l.

    rel_rec_r. rel_pure_r. rel_alloc_r cl as "Hcl".
    do 2 rel_pure_r. rel_newproph_r p.
    do 2 rel_pure_r.
    rel_apply_r refines_newlock_r. iIntros (lk) "Hlk".
    do 2 rel_pure_r.
    iMod (inv_alloc coinN _
           (∃ (b : bool), is_locked_r lk false
                        ∗ ce ↦ #b
                        ∗ (cl ↦ₛ NONEV ∨ cl ↦ₛ SOMEV #b))%I
            with "[$]") as "#Hinv".
    iApply refines_pair.
    - rel_pure_l; rel_pure_r. iApply refines_arrow. iIntros (??) "!> _".
      rel_pure_l; rel_rec_l; rel_pure_r; rel_rec_r. repeat rel_pure_l.
      rel_load_l_atomic. iInv coinN as (b) "(Hlk & Hce & H)" "Hclose".
      iModIntro. iFrame. iNext. iIntros "Hce". repeat rel_pure_r.
      rel_apply_r (refines_acquire_r with "Hlk"). iIntros "Hlk".
      repeat rel_pure_r.
      iDestruct "H" as "[Hcl|Hcl]"; rel_load_r; repeat rel_pure_r.
      + rel_apply_r (refines_rand_r b). repeat rel_pure_r.
        rel_store_r. repeat rel_pure_r.
        rel_resolveproph_r. repeat rel_pure_r.
        rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        repeat rel_pure_r. iMod ("Hclose" with "[$]") as "_".
        rel_values.
      + rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        repeat rel_pure_r. iMod ("Hclose" with "[$]") as "_".
        rel_values.
    - rel_pure_l; rel_pure_r. iApply refines_arrow. iIntros (??) "!> _".
      rel_pure_l; rel_rec_l; rel_pure_r; rel_rec_r. repeat rel_pure_l.
      rel_apply_l refines_rand_l. iNext. iIntros (b).
      rel_store_l_atomic. iInv coinN as (b') "(Hlk & Hce & H)" "Hclose".
      iModIntro. iFrame. iNext. iIntros "Hce". repeat rel_pure_r.
      rel_apply_r (refines_acquire_r with "Hlk"). iIntros "Hlk".
      repeat rel_pure_r.
      iDestruct "H" as "[Hcl|Hcl]"; rel_store_r; repeat rel_pure_r.
      + rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        repeat rel_pure_r. iMod ("Hclose" with "[$]") as "_".
        rel_values.
      + rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        repeat rel_pure_r. iMod ("Hclose" with "[$]") as "_".
        rel_values.
  Qed.

  (** Finally we show that we can get rid of prophecy instrumentation. *)
  Lemma coin_lazy'_lazy_refinement :
    ⊢ REL coin2' << coin2 : (() → lrel_bool) * (() → ()).
  Proof.
    unfold coin2, coin2'.
    rel_rec_l. rel_pure_l. rel_alloc_l c' as "Hc'".
    do 2 rel_pure_l. rel_newproph_l vs p as "Hp".
    do 2 rel_pure_l.

    rel_rec_r. rel_pure_r. rel_alloc_r c as "Hc".
    do 2 rel_pure_r.

    rel_apply_l (refines_newlock_l coinN
        (∃ vs, proph p vs ∗
          (c' ↦ NONEV ∗ c ↦ₛ NONEV
          ∨ ∃ (b : bool), c' ↦ SOMEV #b ∗ c ↦ₛ SOMEV #b))%I
      with "[-]").
    { iExists vs. iFrame. iRight. iExists false. iFrame. }
    clear vs.
    iNext. iIntros (lk γ) "#Hlk /=". do 2 rel_pure_l.
    iApply refines_pair.
    - rel_pure_l; rel_pure_r. iApply refines_arrow. iIntros (??) "!> _".
      rel_pure_l; rel_rec_l; rel_pure_r; rel_rec_r. repeat rel_pure_l.
      rel_apply_l (refines_acquire_l with "Hlk").
      iNext. iIntros "Hlocked".
      iDestruct 1 as (vs) "[Hp H]". repeat rel_pure_l.
      iDestruct "H" as "[[Hc' Hc]|H]"; last iDestruct "H" as (x) "[Hc' Hc]";
        rel_load_l; rel_load_r; repeat rel_pure_l.
      + rel_apply_l refines_rand_l. iNext. iIntros (b).
        repeat rel_pure_l. rel_store_l. repeat rel_pure_l.
        rel_apply_l refines_resolveproph_l. iModIntro. iExists _; iFrame.
        iNext. iIntros (vs' ->) "Hp". repeat rel_pure_l.
        repeat rel_pure_r.
        rel_apply_r (refines_rand_r b). repeat rel_pure_r.
        rel_cmpxchg_suc_r. repeat rel_pure_r.
        rel_apply_l (refines_release_l with "Hlk Hlocked [-]").
        { iExists vs'. iFrame. iRight. iFrame. }
        iNext. repeat rel_pure_l; rel_values.
      + repeat rel_pure_r.
        rel_apply_l (refines_release_l with "Hlk Hlocked [-]").
        { iExists vs. iFrame. iRight. iFrame. }
        iNext. repeat rel_pure_l; rel_values.
    - rel_pure_l; rel_pure_r. iApply refines_arrow. iIntros (??) "!> _".
      rel_pure_l; rel_rec_l; rel_pure_r; rel_rec_r. repeat rel_pure_l.
      rel_apply_l (refines_acquire_l with "Hlk").
      iNext. iIntros "Hlocked".
      iDestruct 1 as (vs) "[Hp H]". repeat rel_pure_l.
      iDestruct "H" as "[[Hc' Hc]|H]"; last iDestruct "H" as (x) "[Hc' Hc]";
        rel_store_l; rel_pure_r; rel_store_r; repeat rel_pure_l.
      + rel_apply_l (refines_release_l with "Hlk Hlocked [-]").
        { eauto with iFrame. }
        iNext. repeat rel_pure_l; rel_values.
      + rel_apply_l (refines_release_l with "Hlk Hlocked [-]").
        { eauto with iFrame. }
        iNext. repeat rel_pure_l; rel_values.
  Qed.

  Lemma coin_lazy_lazy'_refinement :
    ⊢ REL coin2 << coin2' : (() → lrel_bool) * (() → ()).
  Proof.
    unfold coin2, coin2'.
    rel_rec_l. rel_pure_l. rel_alloc_l c as "Hc".
    do 2 rel_pure_l.

    rel_rec_r. rel_pure_r. rel_alloc_r c' as "Hc'".
    do 2 rel_pure_r. rel_newproph_r p.
    do 2 rel_pure_r.

    rel_apply_r refines_newlock_r. iIntros (lk) "Hlk".

    iMod (inv_alloc coinN _
           (is_locked_r lk false
          ∗ (c' ↦ₛ NONEV ∗ c ↦ NONEV
            ∨ ∃ (b : bool), c' ↦ₛ SOMEV #b ∗ c ↦ SOMEV #b))%I
            with "[-]") as "#Hinv".
    { iNext. iFrame. iRight. iFrame. }
    do 2 rel_pure_r.

    iApply refines_pair.
    - rel_pure_l; rel_pure_r.
      iApply refines_arrow. iIntros (??) "!> _". rel_pure_l; rel_pure_r.
      rel_rec_r. repeat rel_pure_r.
      iLöb as "IH". rel_rec_l.
      rel_load_l_atomic. iInv coinN as "(Hlk & [[Hc' Hc]|H])" "Hclose";
        iModIntro.
      + iExists _. iFrame. iNext. iIntros "Hc".
        repeat rel_pure_l.
        iMod ("Hclose" with "[-]") as "_".
        { eauto with iFrame. }
        rel_apply_l refines_rand_l. iNext. iIntros (b).
        repeat rel_pure_l.
        rel_cmpxchg_l_atomic. iInv coinN as "(Hlk & [[Hc' Hc]|H])" "Hclose".
        * iModIntro; iExists _. iFrame. iSplit.
          { iIntros (?); simplify_eq/=. }
          iIntros (_). iNext. iIntros "Hc".
          rel_pures_l. rel_pures_r. rel_apply_r (refines_acquire_r with "Hlk").
          iIntros "Hlk". repeat rel_pure_r. rel_load_r.
          repeat rel_pure_r. rel_apply_r (refines_rand_r b).
          repeat rel_pure_r. rel_store_r.
          repeat rel_pure_r. rel_resolveproph_r.
          repeat rel_pure_r. rel_apply_r (refines_release_r with "Hlk").
          iIntros "Hlk". repeat rel_pure_r.
          iMod ("Hclose" with "[-]") as "_".
          { eauto with iFrame. }
          rel_values.
        * iDestruct "H" as (x) "[Hc' Hc]".
          iModIntro; iFrame. iSplit; last first.
          { iIntros (?); simplify_eq/=. }
          iIntros (_). iNext. iIntros "Hc".
          rel_pures_l.
          iMod ("Hclose" with "[-]") as "_".
          { eauto with iFrame. }
          iApply "IH".
      + iClear "IH".
        iDestruct "H" as (b) "[Hc' Hc]". iFrame. iNext. iIntros "Hc".
        repeat rel_pure_l.
        rel_apply_r (refines_acquire_r with "Hlk").
        iIntros "Hlk". repeat rel_pure_r. rel_load_r.
        repeat rel_pure_r. rel_apply_r (refines_release_r with "Hlk").
        iIntros "Hlk". repeat rel_pure_r.
        iMod ("Hclose" with "[-]") as "_".
        { eauto with iFrame. }
        rel_values.
    - rel_pure_l. rel_pure_r.
      iApply refines_arrow. iIntros (??) "!> _".
      repeat rel_rec_l. repeat rel_rec_r. repeat rel_pure_l. repeat rel_pure_r.
      rel_store_l_atomic. iInv coinN as "(Hlk & [[Hc' Hc]|H])" "Hclose";
        iModIntro.
      + iFrame. iNext. iIntros "Hc".
        rel_apply_r (refines_acquire_r with "Hlk").
        iIntros "Hlk". repeat rel_pure_r. rel_store_r.
        repeat rel_pure_r. rel_apply_r (refines_release_r with "Hlk").
        iIntros "Hlk". repeat rel_pure_r.
        iMod ("Hclose" with "[-]") as "_".
        { eauto with iFrame. }
        rel_values.
      + iDestruct "H" as (x) "[Hc' Hc]".
        iFrame. iNext. iIntros "Hc".
        rel_apply_r (refines_acquire_r with "Hlk").
        iIntros "Hlk". repeat rel_pure_r. rel_store_r.
        repeat rel_pure_r. rel_apply_r (refines_release_r with "Hlk").
        iIntros "Hlk". repeat rel_pure_r.
        iMod ("Hclose" with "[-]") as "_".
        { eauto with iFrame. }
        rel_values.
  Qed.

End proofs.

Theorem coin_lazy_eager_ctx_refinement :
  ∅ ⊨ coin2 ≤ctx≤ coin1 : (() → TBool) * (() → ()).
Proof.
  eapply (ctx_refines_transitive ∅ _).
  - eapply (refines_sound #[relocΣ; lockΣ]).
    iIntros (? Δ). iApply coin_lazy_lazy'_refinement.
  - eapply (refines_sound #[relocΣ; lockΣ]).
    iIntros (? Δ). iApply coin_lazy'_eager_refinement.
Qed.

Theorem coin_eager_lazy_ctx_refinement :
  ∅ ⊨ coin1 ≤ctx≤ coin2 : (() → TBool) * (() → ()).
Proof.
  eapply (ctx_refines_transitive ∅ _).
  - eapply (refines_sound #[relocΣ; lockΣ]).
    iIntros (? Δ). iApply coin_eager_lazy'_refinement.
  - eapply (refines_sound #[relocΣ; lockΣ]).
    iIntros (? Δ). iApply coin_lazy'_lazy_refinement.
Qed.
