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
  let: "st" := ref NIL in
  let: "lk" := newlock #() in
  ("st", "lk")%E.

Definition CG_stack : val := Λ:
  (CG_new_stack, λ: "stt", CG_locked_pop "stt",
    λ: "stt" "x", CG_locked_push "stt" "x").

Fixpoint val_of_list (ls : list val) : val :=
  match ls with
  | [] => NONEV
  | v::vs => CONSV v (val_of_list vs)
  end.

Instance val_to_list_inj : Inj (=@{list val}) (=@{val}) val_of_list.
Proof.
  intros ls1. induction ls1 as [|h1 ls1]=>ls2; destruct ls2; naive_solver.
Qed.

Definition is_stack `{!relocG Σ} (rs : val) (ls : list val) : iProp Σ :=
  ∃ (st : loc) l, ⌜rs = (#st, l)%V⌝ ∗ is_locked_r l false ∗ st ↦ₛ val_of_list ls.

Section rules.
  Context `{!relocG Σ}.

  Lemma refines_CG_push_r rs tl v E t K A :
    nclose relocN ⊆ E →
    is_stack rs tl -∗
    (is_stack rs (v::tl)
      -∗ REL t << fill K (of_val #()) @ E : A) -∗
    REL t << fill K (CG_locked_push rs v) @ E : A.
  Proof.
    iIntros (?). iDestruct 1 as (st l ->) "[Hl Hst]".
    iIntros "Hlog".
    rel_rec_r. repeat rel_pure_r.
    rel_apply_r (refines_acquire_r with "Hl").
    iIntros "Hl". repeat rel_pure_r.
    rel_rec_r. repeat rel_pure_r.
    rel_load_r. repeat rel_pure_r.
    rel_store_r. repeat rel_pure_r.
    rel_apply_r (refines_release_r with "Hl").
    iIntros "Hl".
    iApply ("Hlog" with "[Hst Hl]").
    iExists _,_. eauto with iFrame.
  Qed.

  Lemma refines_CG_pop_suc_r rs w tl E t K A :
    nclose relocN ⊆ E →
    is_stack rs (w::tl) -∗
    (is_stack rs tl -∗
      REL t << fill K (of_val (SOMEV w)) @ E : A) -∗
    REL t << fill K (CG_locked_pop rs) @ E : A.
  Proof.
    iIntros (?). iDestruct 1 as (st l ->) "[Hl Hst]".
    iIntros "Hlog".
    rel_rec_r. repeat rel_pure_r.
    rel_apply_r (refines_acquire_r with "Hl").
    iIntros "Hl". repeat rel_pure_r. rel_rec_r.
    rel_load_r. rel_rec_r. repeat rel_pure_r.
    rel_store_r. repeat rel_pure_r.
    rel_apply_r (refines_release_r with "Hl").
    iIntros "Hl". repeat rel_pure_r.
    iApply ("Hlog" with "[Hst Hl]"). iExists _,_; eauto with iFrame.
  Qed.

  Lemma refines_CG_pop_fail_r rs E t K A :
    nclose relocN ⊆ E →
    is_stack rs [] -∗
    (is_stack rs []
      -∗ REL t << fill K (of_val NONEV) @ E : A) -∗
    REL t << fill K (CG_locked_pop rs) @ E : A.
  Proof.
    iIntros (?). iDestruct 1 as (st l ->) "[Hl Hst]".
    iIntros "Hlog".
    rel_rec_r. repeat rel_pure_r.
    rel_apply_r (refines_acquire_r with "Hl").
    iIntros "Hl". repeat rel_pure_r.
    repeat rel_rec_r.
    rel_load_r. rel_rec_r. repeat rel_pure_r.
    rel_apply_r (refines_release_r with "Hl").
    iIntros "Hl". repeat rel_pure_r.
    iApply ("Hlog" with "[Hst Hl]"). iExists _,_; eauto with iFrame.
  Qed.

End rules.
