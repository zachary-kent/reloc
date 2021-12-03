From reloc Require Import reloc lib.lock lib.list.

(* The course-grained queue is implemented as a linked list guarded by a
   lock. *)

Definition CG_dequeue_go : val := λ: "head",
  match: !"head" with
    NONE => #() #() (* Stuck. *)
  | SOME "p" => "head" <- (Snd "p");; Fst "p"
  end.

Definition CG_dequeue : val := λ: "lock" "head" <>,
  acquire "lock" ;;
  let: "v" := CG_dequeue_go "head" in
  release "lock" ;;
  "v".

Definition CG_enqueue_go : val := rec: "enqueue" "x" "head" :=
  match: "head" with
    NONE => CONS "x" NIL
  | SOME "p" => CONS (Fst "p") ("enqueue" "x" (Snd "p"))
  end.

Definition CG_enqueue : val := λ: "lock" "head" "x",
  acquire "lock" ;;
  "head" <- CG_enqueue_go "x" (! "head") ;;
  release "lock".

Definition CG_queue : val := Λ:
  let: "head" := ref NIL in
  let: "lock" := newlock #() in
  ((λ: "x", CG_enqueue "lock" "head" "x"),
   (λ: "x", CG_dequeue "lock" "head" "x")).

Section CG_queue.
  Context `{relocG Σ}.

  (* Representation predicate for the course grained queue. *)
  Fixpoint isCGQueue_go (xs : list val) : val :=
    match xs with
    | nil => NILV
    | x :: xs' => (CONSV x (isCGQueue_go xs'))
    end.

  Definition cgQueueInv (ℓ : loc) lk (xs : list val) : iProp Σ :=
    ℓ ↦ₛ (isCGQueue_go xs) ∗ is_locked_r lk false.

  Lemma refines_CG_enqueue_body_r E t (K : Datatypes.list (ectxi_language.ectx_item heap_ectxi_lang)) A x xs :
    nclose relocN ⊆ E →
    (REL t << fill K (isCGQueue_go (xs ++ [x])) @ E : A) -∗
    (REL t << fill K (CG_enqueue_go x (isCGQueue_go xs)) @ E : A).
  Proof.
    iIntros (HNE) "H".
    iInduction xs as [|x' xs'] "IH" forall (K). simpl.
    - rel_rec_r. rel_pures_r. rel_pures_r.
      iApply "H".
    - simpl.
      rel_rec_r. rel_pures_r. rel_pures_r. rel_apply_r ("IH").
      rel_pures_r. done.
  Qed.

  Lemma refines_CG_enqueue_r list lk E t A x xs :
    nclose relocN ⊆ E →
    cgQueueInv list lk xs -∗
    (cgQueueInv list lk (xs ++ [x]) -∗ REL t << #() @ E : A) -∗
    REL t << (CG_enqueue lk #list x) @ E : A.
  Proof.
    iIntros (HNE) "[pts lofal] H".
    rewrite /CG_enqueue.
    rel_pures_r.
    rel_apply_r (refines_acquire_r with "lofal"). iIntros "lotru".
    rel_pures_r.
    rel_load_r.
    rel_apply_r (refines_CG_enqueue_body_r).
    rel_pures_r.
    rel_store_r.
    rel_pures_r.
    rel_apply_r (refines_release_r with "lotru"). iIntros "lofal".
    iApply "H".
    iFrame.
  Qed.

  Lemma refines_right_CG_dequeue E k lk list x xs :
    nclose relocN ⊆ E →
    cgQueueInv list lk (x :: xs) -∗
    refines_right k (CG_dequeue lk #list #()) ={E}=∗
    cgQueueInv list lk (xs) ∗ refines_right k (of_val x).
  Proof.
    iIntros (HNE) "[pts lofal] H". simpl.
    rewrite /CG_dequeue /CG_dequeue_go /is_locked_r.
    iDestruct "lofal" as (ℓk ->)  "Hlk".
    tp_pures k.
    tp_rec k.
    tp_cmpxchg_suc k.
    tp_pures k.
    tp_load k.
    tp_pures k.
    tp_store k.
    tp_pures k.
    tp_rec k.
    tp_store k.
    tp_pures k.
    iModIntro. iFrame "H". rewrite /cgQueueInv. iFrame "pts".
    iExists _. by iFrame.
  Qed.

  Lemma refines_CG_dequeue_cons_r E t A lk list x xs :
    nclose relocN ⊆ E →
    cgQueueInv list lk (x :: xs) -∗
    (cgQueueInv list lk xs -∗ REL t << x @ E : A) -∗
    REL t << (CG_dequeue lk #list #()) @ E : A.
  Proof.
    iIntros (HNE) "H1 H2".
    iApply refines_split. iIntros (k) "Hk".
    iMod (refines_right_CG_dequeue with "H1 Hk") as "[H1 Hk]"; first done.
    iSpecialize ("H2" with "H1").
    iApply (refines_combine with "H2 Hk").
  Qed.

End CG_queue.
