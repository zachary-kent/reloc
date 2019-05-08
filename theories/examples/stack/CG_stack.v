(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Coarse-grained linearizable stack *)
From reloc Require Export reloc lib.lock lib.list.

(* Stack τ = (μ x. Unit + (τ * x)) * lock) , essentially a type of
lists & a mutex. *)

(* Coarse-grained push *)
Program Definition CG_push : val := λ: "st" "x",
  "st" <- CONS "x" (!"st").

Definition CG_locked_push : val := λ: "stt" "x",
  acquire (Snd "stt");; CG_push (Fst "stt") "x";; release (Snd "stt").

(* pop s = λ x. match (load s) with
                | nil => InjL ()
                | cons y ys => s <- ys ;; InjR y
                end *)
Definition CG_pop : val := λ: "st",
  match: rec_unfold !"st" with
    NONE => NONE
  | SOME "y" => "st" <- (Snd "y");; SOME (Fst "y")
  end.

Definition CG_locked_pop : val := λ: "stt",
  acquire (Snd "stt");;
  let: "v" := CG_pop (Fst "stt") in
  release (Snd "stt");; "v".

Definition CG_new_stack : val := λ: <>,
  (ref NIL, newlock #())%E.

Definition CG_stack : val := Λ:
  (CG_new_stack, λ: "stt", CG_locked_pop "stt",
    λ: "stt" "x", CG_locked_push "stt" "x").

Section rules.
  Context `{relocG Σ}.

  Lemma refines_CG_push_r st l (v w : val) E t K A :
    nclose relocN ⊆ E →
    st ↦ₛ v -∗ is_lock_r l Unlocked_r -∗
    (st ↦ₛ SOMEV (w, v) -∗ is_lock_r l Unlocked_r
      -∗ REL t << fill K (of_val #()) @ E : A) -∗
    REL t << fill K (CG_locked_push (#st, l)%V w) @ E : A.
  Proof.
    iIntros (?) "Hst Hl Hlog".
    rel_rec_r. repeat rel_pure_r.
    rel_apply_r (refines_acquire_r with "Hl").
    iIntros "Hl". repeat rel_pure_r.
    rel_rec_r. repeat rel_pure_r.
    rel_load_r. repeat rel_pure_r.
    rel_store_r. repeat rel_pure_r.
    rel_apply_r (refines_release_r with "Hl").
    iIntros "Hl".
    iApply ("Hlog" with "Hst Hl").
  Qed.

  Lemma refines_CG_pop_suc_r st l (w v : val) E t K A :
    nclose relocN ⊆ E →
    st ↦ₛ SOMEV (w, v) -∗
    is_lock_r l Unlocked_r -∗
    (st ↦ₛ v -∗ is_lock_r l Unlocked_r
      -∗ REL t << fill K (of_val (SOMEV w)) @ E : A) -∗
    REL t << fill K (CG_locked_pop (#st, l)%V) @ E : A.
  Proof.
    iIntros (?) "Hst Hl Hlog".
    rel_rec_r. repeat rel_pure_r.
    rel_apply_r (refines_acquire_r with "Hl").
    iIntros "Hl". repeat rel_pure_r. rel_rec_r.
    rel_load_r. rel_rec_r. repeat rel_pure_r.
    rel_store_r. repeat rel_pure_r.
    rel_apply_r (refines_release_r with "Hl").
    iIntros "Hl". repeat rel_pure_r.
    iApply ("Hlog" with "Hst Hl").
  Qed.

  Lemma refines_CG_pop_fail_r st l E t K A :
    nclose relocN ⊆ E →
    st ↦ₛ NONEV -∗
    is_lock_r l Unlocked_r -∗
    (st ↦ₛ NONEV -∗ is_lock_r l Unlocked_r
      -∗ REL t << fill K (of_val NONEV) @ E : A) -∗
    REL t << fill K (CG_locked_pop (#st, l)%V) @ E : A.
  Proof.
    iIntros (?) "Hst Hl Hlog".
    rel_rec_r. repeat rel_pure_r.
    rel_apply_r (refines_acquire_r with "Hl").
    iIntros "Hl". repeat rel_pure_r.
    repeat rel_rec_r.
    rel_load_r. rel_rec_r. repeat rel_pure_r.
    rel_apply_r (refines_release_r with "Hl").
    iIntros "Hl". repeat rel_pure_r.
    iApply ("Hlog" with "Hst Hl").
  Qed.

End rules.
