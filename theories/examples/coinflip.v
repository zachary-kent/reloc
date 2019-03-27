From iris.heap_lang Require Import lifting.
From reloc Require Import reloc lib.lock.

(* for rand (), val_to_bool *)
From reloc.examples Require Import lateearlychoice.

Definition newcoin : val := λ: <>, ref #false.
Definition flip : val := λ: "c" <>, "c" <- rand #().
Definition read : val := λ: "c" <>, !"c".

Definition newcoin_lazy : val := λ: <>, ref (SOME #false).

Definition flip_lazy : val := λ: "c" "lk" "p" <>,
  acquire "lk";;
  "c" <- NONE;;
  release "lk".

Definition read_lazy : val := λ: "c" "lk" "p" <>,
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
  (read "c", flip "c").
Definition coin2 : expr :=
  let: "c" := newcoin_lazy #() in
  let: "p" := NewProph in
  let: "lk" := newlock #() in
  (read_lazy "c" "lk" "p", flip_lazy "c" "lk" "p").

Section proofs.
  Context `{!relocG Σ, !lockG Σ}.

  Definition coinN := nroot.@"coins".

  Definition I (cl ce : loc) (p : proph_id) :=
    (∃ vs : list val, proph p vs ∗
    (cl ↦ NONEV ∗ ce ↦ₛ #(val_to_bool vs)
    ∨ ∃ (b:bool), cl ↦ SOMEV #b ∗ ce ↦ₛ #b))%I.

  Lemma coin_lazy_eager_refinement :
    REL coin2 << coin1 : (() → lrel_bool) * (() → ()).
  Proof.
    unfold coin1, coin2.
    rel_rec_r. rel_alloc_r ce as "Hce". do 2 rel_pure_r.

    rel_rec_l. rel_pure_l. rel_alloc_l cl as "Hcl".
    do 2 rel_pure_l. rel_newproph_l vs p as "Hp".
    do 2 rel_pure_l.
    rel_apply_l (refines_newlock_l coinN (I cl ce p) with "[-]").
    { iExists vs. iFrame. iRight. iExists false. iFrame. }
    clear vs.
    iNext. iIntros (lk γ) "#Hlk /=". do 2 rel_pure_l.
    iApply refines_pair.
    - rel_rec_l. repeat rel_pure_l.
      rel_rec_r. repeat rel_pure_r.
      iApply refines_arrow. iModIntro. iIntros (??) "_".
      rel_pure_l. rel_pure_r.
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
    - rel_rec_l. repeat rel_pure_l.
      rel_rec_r. repeat rel_pure_r.
      iApply refines_arrow. iModIntro. iIntros (??) "_".
      rel_pure_l. rel_pure_r.
      rel_apply_l (refines_acquire_l with "Hlk").
      iNext. iIntros "Hlocked".
      iDestruct 1 as (vs) "[Hp H]". repeat rel_pure_l.
      iDestruct "H" as "[[Hcl Hce]|H]"; last iDestruct "H" as (x) "[Hcl Hce]";
        rel_store_l; repeat rel_pure_l.
      + rel_apply_r (refines_rand_r (val_to_bool vs)).
        rel_store_r.
        rel_apply_l (refines_release_l with "Hlk Hlocked [-]").
        { iExists vs. iFrame. iLeft. iFrame. }
        iNext. rel_values.
      + rel_apply_r (refines_rand_r (val_to_bool vs)).
        rel_store_r.
        rel_apply_l (refines_release_l with "Hlk Hlocked [-]").
        { iExists vs. iFrame. iLeft. iFrame. }
        iNext. rel_values.
  Qed.

  (* this part is easier *)
  Lemma coin_eager_lazy_refinement :
    REL coin1 << coin2 : (() → lrel_bool) * (() → ()).
  Proof.
    unfold coin1, coin2.
    rel_rec_l. rel_alloc_l ce as "Hce". do 2 rel_pure_l.

    rel_rec_r. rel_pure_r. rel_alloc_r cl as "Hcl".
    do 2 rel_pure_r. rel_newproph_r p.
    do 2 rel_pure_r.
    rel_apply_r refines_newlock_r. iIntros (lk) "Hlk".
    do 2 rel_pure_r.
    iMod (inv_alloc coinN _
           (∃ (b : bool), lk ↦ₛ #false
                        ∗ ce ↦ #b
                        ∗ (cl ↦ₛ NONEV ∨ cl ↦ₛ SOMEV #b))%I
            with "[-]") as "#Hinv".
    { iNext. iExists false. iFrame. }
    iApply refines_pair.
    - rel_rec_l. repeat rel_pure_l.
      rel_rec_r. repeat rel_pure_r.
      iApply refines_arrow. iModIntro. iIntros (??) "_".
      rel_pure_l. rel_pure_r.
      rel_load_l_atomic. iInv coinN as (b) "(Hlk & Hce & H)" "Hclose".
      iModIntro. iExists _. iFrame. iNext. iIntros "Hce".
      rel_apply_r (refines_acquire_r with "Hlk"). iIntros "Hlk".
      repeat rel_pure_r.
      iDestruct "H" as "[Hcl|Hcl]"; rel_load_r; repeat rel_pure_r.
      + rel_apply_r (refines_rand_r b). repeat rel_pure_r.
        rel_store_r. repeat rel_pure_r.
        rel_apply_r refines_resolveproph_r. repeat rel_pure_r.
        rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        repeat rel_pure_r. iMod ("Hclose" with "[-]") as "_".
        { eauto with iFrame. }
        rel_values.
      + rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        repeat rel_pure_r. iMod ("Hclose" with "[-]") as "_".
        { eauto with iFrame. }
        rel_values.
    - rel_rec_l. repeat rel_pure_l.
      rel_rec_r. repeat rel_pure_r.
      iApply refines_arrow. iModIntro. iIntros (??) "_".
      rel_pure_l. rel_pure_r.
      rel_apply_l refines_rand_l. iNext. iIntros (b).
      rel_store_l_atomic. iInv coinN as (b') "(Hlk & Hce & H)" "Hclose".
      iModIntro. iExists _. iFrame. iNext. iIntros "Hce".
      rel_apply_r (refines_acquire_r with "Hlk"). iIntros "Hlk".
      repeat rel_pure_r.
      iDestruct "H" as "[Hcl|Hcl]"; rel_store_r; repeat rel_pure_r.
      + rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        repeat rel_pure_r. iMod ("Hclose" with "[-]") as "_".
        { eauto with iFrame. }
        rel_values.
      + rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
        repeat rel_pure_r. iMod ("Hclose" with "[-]") as "_".
        { eauto with iFrame. }
        rel_values.
  Qed.

End proofs.

Theorem coin_lazy_eager_ctx_refinement :
  ∅ ⊨ coin2 ≤ctx≤ coin1 : (TUnit → TBool) * (TUnit → TUnit).
Proof.
  eapply (refines_sound #[relocΣ; lockΣ]).
  iIntros (? Δ). iApply coin_lazy_eager_refinement.
Qed.

Theorem coin_eager_lazy_ctx_refinement :
  ∅ ⊨ coin1 ≤ctx≤ coin2 : (TUnit → TBool) * (TUnit → TUnit).
Proof.
  eapply (refines_sound #[relocΣ; lockΣ]).
  iIntros (? Δ). iApply coin_eager_lazy_refinement.
Qed.

