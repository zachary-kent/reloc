(* ReLoC -- Relational logic for fine-grained concurrency *)
(** (Concurrent) Kleene algebra laws.

    This is still WIP.

    We consider well-typed terms quotiented out by contextual equivalence:
          { e | ⊢ₜ e : TUnit } / =ctx=
    and show that this is almost a model of Concurrent Kleene Algebra
*)

From reloc Require Export reloc.
From reloc.examples Require Export or par.
Set Default Proof Using "Type".

Notation "⊥" := (bot #()).

Ltac use_logrel :=
  eapply (refines_sound #[relocΣ;spawnΣ]); iIntros (? Δ).
Tactic Notation "use_logrel/=" :=
  use_logrel; rel_pures_l; rel_pures_r.


Lemma typed_is_closed_empty e τ :
  ∅ ⊢ₜ e : τ → is_closed_expr [] e.
Proof.
  intros H%typed_is_closed. revert H.
  by rewrite dom_empty_L elements_empty.
Qed.

Ltac fundamental := by iApply (refines_typed TUnit []).
Ltac closedness := by (eapply typed_is_closed_empty; eauto).

Lemma plus_zero e :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊨ (e ⊕ ⊥) =ctx= e : TUnit.
Proof.
  intros He. split.
  - use_logrel/=. iApply or_bot_l. fundamental.
  - use_logrel/=. iApply or_bot_r. fundamental.
Qed.

Lemma plus_idemp e :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊨ (e ⊕ e) =ctx= e : TUnit.
Proof.
  intros He. split.
  - use_logrel/=. iApply or_idemp_l. fundamental.
  - use_logrel/=. iApply or_idemp_r. fundamental.
Qed.

Lemma plus_comm e f :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊢ₜ f : TUnit →
  ∅ ⊨ (e ⊕ f) =ctx= (f ⊕ e) : TUnit.
Proof.
  intros He Hf. split; use_logrel/=; iApply or_comm; fundamental.
Qed.

Lemma plus_assoc e f g :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊢ₜ f : TUnit →
  ∅ ⊢ₜ g : TUnit →
  ∅ ⊨ (e ⊕ f) ⊕ g =ctx= e ⊕ (f ⊕ g) : TUnit.
Proof.
  intros He Hf Hg. split.
  - use_logrel. iApply or_assoc_r; fundamental.
  - use_logrel. iApply or_assoc_l; fundamental.
Qed.

Lemma mult_assoc e f g :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊢ₜ f : TUnit →
  ∅ ⊢ₜ g : TUnit →
  ∅ ⊨ ((e ;; f) ;; g) =ctx= (e ;; (f ;; g)) : TUnit.
Proof.
  intros He Hf Hg. split.
  - use_logrel/=.
    rel_bind_l e. rel_bind_r e.
    iApply refines_bind; first by fundamental.
    iIntros (? ?) "_ /=". rel_pures_l. rel_pures_r.
    iApply (refines_typed TUnit []). by apply Seq_typed.
  - use_logrel/=.
    rel_bind_l e. rel_bind_r e.
    iApply refines_bind; first by fundamental.
    iIntros (? ?) "_ /=". rel_pures_l. rel_pures_r.
    iApply (refines_typed TUnit []). by apply Seq_typed.
Qed.

Lemma mult_distr_plus_l e f g :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊢ₜ f : TUnit →
  ∅ ⊢ₜ g : TUnit →
  ∅ ⊨ (e ;; (f ⊕ g)) =ctx= ((e ;; f) ⊕ (e ;; g)) : TUnit.
Proof.
  intros He Hf Hg. split.
  - (* intermediate instrumented program *)
    pose (P := (let: "p" := NewProph in
         e;;
         (((resolve_proph: "p" to: #0);; f) ⊕
          ((resolve_proph: "p" to: #1);; g)))%E).
    eapply (ctx_refines_transitive ∅ TUnit _ P).
    + use_logrel. iApply seq_or_2_instrument; (fundamental || closedness).
    + use_logrel. iApply seq_or_2'; (fundamental || closedness).
  - use_logrel. iApply seq_or_1; fundamental.
Qed.

Lemma mult_distr_plus_r e f g :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊢ₜ f : TUnit →
  ∅ ⊢ₜ g : TUnit →
  ∅ ⊨ ((e ⊕ f) ;; g) =ctx= ((e ;; g) ⊕ (f ;; g)) : TUnit.
Proof.
  intros He Hf Hg. split.
  - use_logrel. iApply or_seq_1; fundamental.
  - use_logrel. iApply or_seq_2; fundamental.
Qed.

Lemma mult_one_r e :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊨ (e ;; #()) =ctx= e : TUnit.
Proof.
  intros He. split.
  - use_logrel. rel_bind_l e. rel_bind_r e.
    iApply refines_bind; first by fundamental.
    iIntros (? ?) "[-> ->] /=". rel_pures_l.
    rel_values.
  - use_logrel. rel_bind_l e. rel_bind_r e.
    iApply refines_bind; first by fundamental.
    iIntros (? ?) "[-> ->] /=". rel_pures_r.
    rel_values.
Qed.

Lemma mult_one_l e :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊨ (#() ;; e) =ctx= e : TUnit.
Proof.
  intros He. split; use_logrel; rel_pures_l; rel_pures_r; fundamental.
Qed.

Lemma mult_zero_r e :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊨ (e ;; ⊥) =ctx= ⊥ : TUnit.
Proof.
  intros He. split.
  - use_logrel.
    (* TODO!!! we need unary interpretation to show that e is safe *)
    Abort.
  (* - use_logrel. rel_apply_l bot_l. *)

Lemma mult_zero_l e :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊨ (⊥ ;; e) =ctx= ⊥ : TUnit.
Proof.
  intros He. split; use_logrel; rel_apply_l bot_l.
Qed.

Notation "e ∥ f" := ((e ||| f);; #())%E (at level 60).

Lemma par_comm e f :
  ∅ ⊢ₜ e : TUnit →
  ∅ ⊢ₜ f : TUnit →
  ∅ ⊨ (e ∥ f) =ctx= (f ∥ e) : TUnit.
Proof.
  intros He Hf. split.
  - use_logrel.
    iApply par_comm; (fundamental || closedness).
  - use_logrel.
    iApply par_comm; (fundamental || closedness).
Qed.

Definition star : val := rec: "star" "f" :=
  #() ⊕ ("f" #();; "star" "f").

Notation "e **" := (star (λ: <>, e)%V) (at level 80).

Section rules.
  Context `{relocG Σ}.

  Lemma star_compatible e e' :
    □ (REL e << e' : ()) -∗
    REL e ** << e' ** : ().
  Proof.
    iIntros "#He". iLöb as "IH". rel_rec_l. rel_rec_r.
    repeat rel_pure_l. repeat rel_pure_r.
    iApply or_compatible; first by rel_values.
    iApply refines_seq.
    - rel_pure_l. rel_pure_r. iAssumption.
    - iApply "IH".
  Qed.

  (* Lemma star_refines_l e t : *)
  (*   REL e ** << t : (). *)
  (* Proof. *)
  (*   iIntros "H". rel_rec_l. repeat rel_pure_l. *)
  (*   iApply or_compatible; first by rel_values. *)
  (*   iApply refines_seq. *)
  (*   - rel_pure_l. rel_pure_r. iAssumption. *)
  (*   - iApply "IH". *)

  Lemma star_id_1 e e' :
    □(REL e << e' : ()) -∗
    REL e ** << (#() ⊕ (e';; e' **))%V : ().
  Proof.
    iIntros "#He".
    rel_rec_l. repeat rel_pure_l. repeat rel_pure_r.
    iApply or_compatible; first by rel_values.
    iApply refines_seq.
    - rel_pure_l. iAssumption.
    - by iApply star_compatible.
  Qed.

  Lemma star_id_2 e e' :
    □(REL e << e' : ()) -∗
    REL (#() ⊕ (e;; e **))%V << e' ** : ().
  Proof.
    iIntros "#He". rel_rec_r. repeat rel_pure_r.
    iApply or_compatible; first by rel_values.
    iApply refines_seq.
    - rel_pure_r. iAssumption.
    - by iApply star_compatible.
  Qed.

  Lemma star_fp e f g :
    □ (WP f {{ _, True }}) -∗
    (REL (e ⊕ (f;; g))%V << g : ()) -∗
    REL (f **;; e) << g : ().
  Proof.
    iIntros "#Hf H". iLöb as "IH".
    rel_rec_l. repeat rel_pure_l.
    rel_apply_l or_refines_l. iSplit.
    - repeat rel_pure_l. (* need transitivity with "H" *) admit.
    - repeat rel_pure_l. (* need that `f` is safe *)
      rel_bind_l f. iApply refines_wp_l. iApply (wp_wand with "Hf").
      iIntros (v) "_". simpl. repeat rel_pure_l. clear v.
      by iApply "IH".
  Abort.

End rules.
