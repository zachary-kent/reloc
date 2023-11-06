From reloc Require Import reloc lib.lock.
From iris.algebra Require Import numbers csum excl auth list gmap gset.
From iris.bi.lib Require Export fixpoint.

From reloc.examples.folly_queue Require Import
    set turnSequencer singleElementQueue CG_queue mpmcqueue.

Definition queueN : namespace := nroot .@ "queue".

(* Setup the cameras. *)

(* We use a finite map from nats to represent a list. *)
Definition listUR := authUR (gmapUR nat (agreeR valO)).

(* LP stepping requests. *)
Definition requestReg := gmap nat ref_id.
Definition requestRegR := authR $ gmapUR nat (agreeR ref_idO).

Class queueG Σ := {
  queue_listUR :: inG Σ listUR;
  queue_requestUR :: inG Σ requestRegR;
}.

(* For the [lia] tactic. *)
(* To support Z.div, Z.modulo, Z.quot, and Z.rem: *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(* Begin hooks to make `lia` work with Nat.modulo and Nat.div *)
Require Import Arith ZArith ZifyClasses ZifyInst Lia.

Global Program Instance Op_Nat_mod : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp Op_Nat_mod.

Global Program Instance Op_Nat_div : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp Op_Nat_div.

(* lia now works with Nat.modulo nad Nat.div. *)

Section queue_refinement.
  Context `{!relocG Σ, !TSG Σ, !queueG Σ}.

  (* A few lemmas and definitions related to the ghost list.

     The ghost list keeps track of _all_ elements that have been enqueued in the
     queue. Including those that are no longer in the queue (they have been
     dequeued). *)

  Lemma list_to_map_snoc {B : Type} l i x :
    i ∉ l.*1 →
    list_to_map (l ++ [(i, x)]) = <[i:=x]> (list_to_map l : gmap nat B).
  Proof.
    intros Hnd.
    induction l as [|[i' x'] l' IH].
    - done.
    - apply not_elem_of_cons in Hnd.
      simpl in *. rewrite IH. 2: { apply Hnd. }
      rewrite insert_commute; first done.
      rewrite comm.
      apply Hnd.
  Qed.

  Definition list_idx_to_map {A : Type} (l : list A) : gmap nat A :=
    list_to_map (zip (seq 0 (length l)) l).

  Lemma list_idx_to_map_append {B : Type} xs (x : B) :
    list_idx_to_map (xs ++ [x]) = <[length xs := x]>(list_idx_to_map xs).
  Proof.
    rewrite /list_idx_to_map.
    rewrite app_length /= Nat.add_1_r.
    rewrite seq_S /=.
    rewrite zip_with_app /=.
    2: { by rewrite seq_length. }
    rewrite list_to_map_snoc; first done.
    rewrite fst_zip. 2: { rewrite seq_length. done. }
    intros [i Hl]%elem_of_list_lookup_1.
    apply lookup_seq in Hl as Hlm.
    simpl in Hlm.
    destruct Hlm as [-> Hlm].
    lia.
  Qed.

  Definition make_map (m : gmap nat val) : gmapUR nat (agreeR valO) :=
    to_agree <$> m.

  Lemma dom_make_map (m : gmap nat val) : dom (make_map m) = dom m.
  Proof.
    rewrite /make_map. rewrite dom_fmap_L. done.
  Qed.

  Lemma make_map_empty : make_map ∅ = ∅.
  Proof. rewrite /make_map. apply: fmap_empty. Qed.

  Definition ghost_list γl (xs : list val) := own γl (● make_map (list_idx_to_map xs)).

  Definition ghost_list_pointsto γl i (x : val) := own γl (◯ {[i := to_agree x]}).

  Lemma ghost_list_alloc : ⊢ |==> ∃ γl, ghost_list γl [].
    iMod (own_alloc (● ∅ : listUR)) as (γl) "Hauth"; first by apply auth_auth_valid.
    rewrite /ghost_list. rewrite make_map_empty.
    iModIntro. iExists _. done.
  Qed.

  Lemma ghost_list_append γl xs (x : val) :
    ghost_list γl xs ==∗ ghost_list γl (xs ++ [x]) ∗ ghost_list_pointsto γl (length xs) x.
  Proof.
    iIntros "HL".
    rewrite /ghost_list /ghost_list_pointsto.
    rewrite -(own_op γl).
    iApply (own_update with "HL").
    apply auth_update_alloc.
    rewrite list_idx_to_map_append.
    rewrite /make_map fmap_insert.
    apply alloc_singleton_local_update; last done.
    rewrite /list_idx_to_map.
    rewrite lookup_fmap.
    rewrite not_elem_of_list_to_map_1; first done.
    rewrite fst_zip. 2: { rewrite seq_length. done. }
    rewrite elem_of_list_In.
    rewrite in_seq. lia.
  Qed.

  Lemma dom_list_to_map {B : Type} (l : list (nat * B)) :
    dom (list_to_map l : gmap nat B) = list_to_set l.*1.
  Proof.
    induction l as [|?? IH].
    - rewrite dom_empty_L. done.
    - rewrite dom_insert_L. rewrite IH. done.
  Qed.

  Lemma ghost_list_le γl xs i x :
    ghost_list γl xs -∗ ghost_list_pointsto γl i x -∗ ⌜i < length xs⌝.
  Proof.
    rewrite /ghost_list /ghost_list_pointsto /list_idx_to_map.
    iIntros "Ha Hb".
    iCombine "Ha Hb" gives %[Hincl _]%auth_both_valid_discrete.
    apply dom_included in Hincl.
    rewrite dom_singleton_L in Hincl.
    rewrite dom_make_map in Hincl.
    rewrite dom_list_to_map in Hincl.
    rewrite fst_zip in Hincl. 2: { rewrite seq_length. done. }
    rewrite list_to_set_seq in Hincl.
    iPureIntro. set_solver.
  Qed.

  Lemma ghost_list_lookup (γl : gname) xs (i : nat) (x : val) :
    xs !! i = Some x →
    ghost_list γl xs ==∗ ghost_list γl xs ∗ ghost_list_pointsto γl i x.
  Proof.
    iIntros (Hs) "Hlist".
    rewrite /ghost_list /ghost_list_pointsto /list_idx_to_map.
    rewrite -own_op.
    iApply (own_update with "Hlist").
    apply: auth_update_dfrac_alloc.
    apply singleton_included_l.
    exists (to_agree x).
    split; last done.
    rewrite lookup_fmap.
    erewrite elem_of_list_to_map_1.
    - simpl. reflexivity.
    - rewrite fst_zip. 2: { rewrite seq_length. done. }
      apply NoDup_seq.
    - apply elem_of_lookup_zip_with.
      exists i, i, x.
      apply lookup_lt_Some in Hs as Lt.
      repeat split; last done.
      apply lookup_seq.
      lia.
  Qed.

  Lemma map_list_snoc γl xs pushTicket popTicket (xn : val) :
    popTicket ≤ pushTicket →
    length xs = pushTicket - popTicket →
    own γl (◯ {[pushTicket := to_agree xn ]}) -∗
    ([∗ list] i↦x ∈ xs, own γl (◯ {[popTicket + i := to_agree x]})) -∗
    [∗ list] i↦x ∈ xs ++ [xn], own γl (◯ {[popTicket + i := to_agree x]}).
  Proof.
    iIntros (Hle Hlen) "Hf Hl".
    rewrite big_sepL_app.
    iFrame.
    simpl.
    replace (popTicket + (length xs + 0)) with (pushTicket) by lia.
    iFrame.
  Qed.

  (* Fragments of the list agree. *)
  Lemma map_list_agree γl i (x x' : val) :
    own γl (◯ {[i := to_agree x]}) -∗
    own γl (◯ {[i := to_agree x']}) -∗
    ⌜x = x'⌝.
  Proof.
    iIntros "A B". iCombine "A B" as "A".
    by iDestruct (own_valid with "A")
      as %Hv%auth_frag_valid%singleton_valid%to_agree_op_inv_L.
    (* by iDestruct (own_valid with "A")
      as %Hv%auth_frag_valid_1%singleton_valid%to_agree_op_inv_L. *)
  Qed.

  Lemma decide_agree γl i (id id' : ref_id) :
    own γl (◯ {[i := to_agree (id : ref_idO)]}) -∗
    own γl (◯ {[i := to_agree (id' : ref_idO)]}) -∗
    ⌜id = id'⌝.
  Proof.
    iIntros "A B". iCombine "A B" as "A".
    by iDestruct (own_valid with "A")
      as %HI%auth_frag_valid%singleton_valid%to_agree_op_inv_L.
  Qed.

  Lemma map_list_elem_of γl m (pushTicket popTicket : nat) (v : val) :
    dom m = set_seq 0 pushTicket →
    own γl (● make_map m) -∗
    own γl (◯ {[popTicket := to_agree v]}) -∗
    ⌜popTicket ∈ set_seq (C:=gset nat) 0 pushTicket⌝.
  Proof.
    iIntros (Hsub) "Ha Hf".
    iCombine "Ha Hf" gives %[H%dom_included _]%auth_both_valid_discrete.
    rewrite dom_make_map in H.
    rewrite Hsub in H.
    rewrite dom_singleton_L in H.
    iPureIntro. set_solver.
  Qed.

  (* A few lemmas related to the tokens. *)

  Definition tokens_from γt n := own γt (set_above n).
  Definition token γt (n : nat) := own γt (set_singleton n).
  Lemma tokens_take γ m : tokens_from γ m ⊢ tokens_from γ (m + 1) ∗ token γ m.
  Proof. rewrite /tokens_from /token -own_op comm -take_first. done. Qed.

  (* A single element queue contains: TS, location, gname for ghost state. *)
  Record seq : Type := MkSeq {
    seq_gname : gname;
    seq_val : val;
  }.

  (* Definition seq_to_val (s : seq) := PairV #s.(seq_ts) #s.(seq_loc). *)

  (* The resource that the i'th SEQ protects in a queue of capacity q.
     Note, j is the the index of the enqueue/dequeue operation we're
     at at the SEQ (a local index). From this we have to "count
     backwards" to compute the index of the enqueue/dequeue operation
     we're at at the queue in total (global index n). *)
  Definition R γl q i (j : nat) (v : val) : iProp Σ :=
    let n := j * q + i
    in ghost_list_pointsto γl n v.

  (* Turn management. *)

  (* Given the total number of push or pop operations that has been carried out,
  ops, returns the number of operations that has affected the i'th SEQ/TS. *)
  Definition nr_of_affecting_ops (q i ops : nat) :=
    (ops / q) + (if i <? ops `mod` q then 1 else 0)%nat.

  (* Helper lemmas *)
  Lemma mod_S_le a b :
    0 < b →
    (a + 1) `mod` b ≤ a `mod` b →
    (a + 1) `mod` b = 0 ∧ a `mod` b = b - 1.
  Proof.
    intros Hob Hab.
    assert (Z.of_nat a = (b * (a `div` b)%Z + (a `mod` b)%Z)%Z)%Z as Ha.
    { lia. }
    destruct (decide ((a `mod` b) < b - 1)) as [Hb|Hb].
    - exfalso.
      cut ((a + 1) `mod` b = a `mod` b + 1)%Z; first lia.
      symmetry. eapply (Zmod_unique _ _ (a `div` b)); lia.
    - assert (a `mod` b = b - 1)%Z as Hamodb by lia.
      split; last lia.
      cut (0 = (a + 1) `mod` b)%Z; first by lia.
      eapply (Zmod_unique _ _ (a `div` b + 1)). lia.
      rewrite {1}Ha Hamodb. lia.
  Qed.

  Lemma mod_S_gt a b :
    0 < b →
    (a + 1) `mod` b > a `mod` b →
    (a + 1) `mod` b = a `mod` b + 1.
  Proof.
    intros Hob Hab.
    assert (Z.of_nat a = (b * (a `div` b)%Z + (a `mod` b)%Z)%Z)%Z as Ha.
    { lia. }
    cut (a `mod` b + 1 = (a + 1) `mod` b)%Z; first lia.
    destruct (decide ((a `mod` b) < b - 1)) as [Hb|Hb].
    - eapply (Zmod_unique _ _ (a `div` b)). lia.
      rewrite {1}Ha. lia.
    - assert (a `mod` b = b - 1)%Z as Hamodb by lia.
      exfalso. lia.
  Qed.

  Lemma nr_of_affecting_ops_0 q i :
    nr_of_affecting_ops q i 0 = 0.
  Proof.
    unfold nr_of_affecting_ops.
    rewrite div0 mod0.
    assert (i <? 0 = false)%nat as ->.
    { apply Nat.ltb_nlt. lia. }
    done.
  Qed.

  Lemma nr_of_affecting_ops_incr q i ops :
    0 < q →
    i < q →
    ops `mod` q ≠ i →
    nr_of_affecting_ops q i (ops + 1) = nr_of_affecting_ops q i ops.
  Proof.
    intros Hgt Hiq Hneq. symmetry.
    rewrite /nr_of_affecting_ops.
    assert (Z.of_nat ops = (q * (ops `div` q)%Z + (ops `mod` q)%Z)%Z)%Z as Hops2.
    { lia. }
    destruct (decide (i < ops `mod` q)) as [Hops|Hops].
    - rewrite ltb_lt_1 //.
      destruct (decide (i < (ops + 1) `mod` q)) as [Hops3|Hops3].
      + rewrite ltb_lt_1 //.
        destruct (decide (ops `mod` q < (ops + 1) `mod` q)) as [Hsucc|Hsucc];
          last first.
        { cut ((ops + 1) `mod` q = 0); first lia.
          eapply mod_S_le; lia. }
        cut (ops `div` q = (ops + 1) `div` q)%Z; first lia.
        eapply (Zdiv_unique _ _ _ (ops `mod` q + 1)); first lia.
        rewrite {1}Hops2. lia.
      + assert (i <? (ops + 1) `mod` q = false)%nat as ->.
        { by apply Nat.ltb_nlt. }
        rewrite Nat.add_0_r.
        destruct (decide ((ops + 1) `mod` q ≤ ops `mod` q)) as [Hsucc|Hsucc]; last lia.
        assert (((ops + 1) `mod` q = 0) ∧ ops `mod` q = q - 1) as [HSmodq Hmodq].
        { eapply mod_S_le; lia. }
        assert (ops + 1 = q * ((ops + 1) `div` q))%Z as Hops4.
        { lia. }
        cut (ops `div` q + 1 = (ops + 1) `div` q)%Z ; first lia.
        eapply (Zdiv_unique _ _ _ 0); lia.
    - assert (i <? ops `mod` q = false)%nat as ->.
      { by apply Nat.ltb_nlt. }
      rewrite Nat.add_0_r.
      destruct (decide (i < (ops + 1) `mod` q)) as [Hops3|Hops3].
      + rewrite ltb_lt_1 //.
        assert (ops `mod` q < (ops + 1) `mod` q) as Hsucc by lia.
        cut (ops `div` q = (ops + 1) `div` q)%Z; first lia.
        eapply (Zdiv_unique _ _ _ (ops `mod` q + 1)); first lia.
        rewrite {1}Hops2. lia.
      + assert (i <? (ops+1) `mod` q = false)%nat as ->.
        { by apply Nat.ltb_nlt. }
        rewrite Nat.add_0_r.
        cut (ops `div` q = (ops + 1) `div` q)%Z; first lia.
        destruct (decide (ops `mod` q < (ops + 1) `mod` q)) as [Hsucc|Hsucc].
        { eapply (Zdiv_unique _ _ _ (ops `mod` q + 1)); first lia.
          rewrite {1}Hops2. lia. }
        exfalso.
        assert ((ops + 1) `mod` q = 0 ∧ ops `mod` q = q - 1) as [HSmod Hmod].
        { eapply mod_S_le; lia. }
        lia.
  Qed.

  Lemma nr_of_affecting_ops_incr_eq q i ops :
    0 < q →
    ops `mod` q = i →
    nr_of_affecting_ops q i (ops + 1) = nr_of_affecting_ops q i ops + 1.
  Proof.
    intros Hgt Heq. symmetry.
    rewrite /nr_of_affecting_ops.
    assert (i <? ops `mod` q = false)%nat as ->.
    { apply Nat.ltb_ge. lia. }
    rewrite Nat.add_0_r.
    assert (Z.of_nat ops = (q * (ops `div` q)%Z + i%Z)%Z)%Z as Hops2.
    { rewrite -Heq. lia. }
    destruct (decide (i < (ops + 1) `mod` q)) as [Hops|Hops].
    - rewrite ltb_lt_1 //.
      assert ((ops + 1) `mod` q = i + 1).
      { rewrite -Heq. eapply mod_S_gt; lia. }
      cut (ops `div` q = (ops + 1) `div` q)%Z; first lia.
      eapply (Zdiv_unique _ _ _ (i+1)); first lia.
      rewrite {1}Hops2. lia.
    - assert ((ops + 1) `mod` q ≤ i) by lia.
      assert (i <? (ops + 1) `mod` q = false)%nat as ->.
      { by apply Nat.ltb_ge. }
      rewrite Nat.add_0_r.
      cut (((ops `div` q) + 1) = (ops + 1) `div` q)%Z; first lia.
      assert (((ops + 1) `mod` q = 0) ∧ ops `mod` q = q - 1) as [HSmodq Hmodq].
      { eapply mod_S_le; lia. }
      assert (ops + 1 = q * ((ops + 1) `div` q))%Z as Hops3.
      { lia. }
      eapply (Zdiv_unique _ _ _ 0); lia.
  Qed.

  (* How many turns have been allocated for a SEQ/TS that has been affected by
  nrPush push operations and nrPop pop operations. NOTE: Since the first turn is
  for a `push` operation for equal values of nrPush and nrPop it is nrPop that
  "dominates" how many tickets have been allocated.
   *)
  (* Definition allocated_turns nrPush nrPop :=
    if decide (nrPush ≤ nrPop) then 2 * nrPop else (2 * nrPush) - 1. *)

  (* Ticket management for the i'th SEQ. *)
  Definition turn_ctx γ q i popTicket pushTicket : iProp Σ :=
    let nrPop := nr_of_affecting_ops q i popTicket in
    let nrPush := nr_of_affecting_ops q i pushTicket in
    enqueue_turns γ nrPush ∗
    dequeue_turns γ nrPop.

  Lemma turn_ctx_initial γ q i : turn_ctx γ q i 0 0 = (enqueue_turns γ 0 ∗ dequeue_turns γ 0)%I.
  Proof.
    rewrite /turn_ctx /nr_of_affecting_ops. autorewrite with natb. done.
  Qed.

  (* If popTicket is advanced in a way that don't affect the i'th TSer then the
  turn_ctx for it does not change. *)
  Lemma turn_ctx_incr_pop γ q i popT pushT :
    0 < q →
    i < q →
    (popT `mod` q ≠ i) →
    turn_ctx γ q i popT pushT ⊢
    turn_ctx γ q i (popT + 1) pushT.
  Proof.
    iIntros (Hgt Hiq Hneq) "Hctx".
    rewrite /turn_ctx (nr_of_affecting_ops_incr q i popT); done.
  Qed.

  Lemma turn_ctx_incr_push γ q i popT pushT :
    0 < q →
    i < q →
    (pushT `mod` q ≠ i) →
    turn_ctx γ q i popT pushT ⊢
    turn_ctx γ q i popT (pushT+1).
  Proof.
    iIntros (Hgt Hiq Hneq) "Hctx".
    rewrite /turn_ctx (nr_of_affecting_ops_incr q i pushT); done.
  Qed.

  Lemma turn_ctx_incr_pop_eq γ q popT pushT :
    0 < q →
    turn_ctx γ q (popT `mod` q) popT pushT ⊢
    turn_ctx γ q (popT `mod` q) (popT + 1) pushT ∗
    dequeue_turn γ (popT `div` q).
  Proof.
    iIntros (Hgt) "[He Hd]".
    rewrite /turn_ctx. iFrame "He".
    rewrite (nr_of_affecting_ops_incr_eq q _ popT); [|lia|lia].
    rewrite /nr_of_affecting_ops.
    assert (_ <? _ = false)%nat as ->.
    { apply Nat.ltb_ge. lia. }
    autorewrite with natb.
    by rewrite dequeue_turns_take.
  Qed.

  Lemma turn_ctx_incr_push_eq γ q popT pushT :
    0 < q →
    turn_ctx γ q (pushT `mod` q) popT pushT ⊢
    turn_ctx γ q (pushT `mod` q) popT (pushT+1) ∗
    enqueue_turn γ (pushT `div` q).
  Proof.
    iIntros (Hgt) "[He Hd]".
    rewrite /turn_ctx. iFrame "Hd".
    rewrite (nr_of_affecting_ops_incr_eq q _ pushT); try lia.
    rewrite /nr_of_affecting_ops.
    assert (_ <? _ = false)%nat as ->.
    { apply Nat.ltb_ge. lia. }
    autorewrite with natb.
    by rewrite enqueue_turns_take.
  Qed.

  (* The invariants. *)

  (* The resources we have for each TSer. *)
  Definition SEQinv γl (q i : nat) (s : seq) popTicket pushTicket :=
    (let (γ, v) := s
     in isSEQ γ (R γl q i) v ∗ turn_ctx γ q i popTicket pushTicket)%I.

  (* The invariant for all SEQs/TSes. *)
  Definition SEQsinv γl q SEQs popTicket pushTicket : iProp Σ :=
    ⌜length SEQs = q⌝ ∧
      [∗ list] i ↦ s ∈ SEQs, SEQinv γl q i s popTicket pushTicket.

  Lemma SEQs_inc_prop_go γl q SEQs popTicket pushTicket v γ :
    0 < q →
    SEQs !! (popTicket `mod` q) = Some (MkSeq γ v) →
    SEQsinv γl q SEQs popTicket pushTicket -∗
    isSEQ γ (R γl q (popTicket `mod` q)) v ∗
    SEQsinv γl q SEQs (popTicket + 1) pushTicket ∗ dequeue_turn γ (popTicket `div` q).
  Proof.
    rewrite /SEQsinv.
    iIntros (Hgt Hlook) "[%Hlen Hs]".
    rewrite (big_sepL_delete' _ _ (popTicket `mod` q)); last done.
    iDestruct "Hs" as "[H Hs]".
    iAssert (
      [∗ list] k↦y ∈ SEQs, ⌜k ≠ popTicket `mod` q⌝ → SEQinv γl q k y (popTicket + 1) pushTicket
    )%I with "[Hs]" as "Hs".
    { iApply (big_sepL_impl with "Hs []").
      iModIntro. iIntros (k x Hlook') "Himpl %Hneq".
      destruct x as [v' γ'].
      iDestruct ("Himpl" $! Hneq) as "[Himpl ho]".
      rewrite /SEQinv. iFrame.
      assert (k < q).
      { rewrite -Hlen. eapply lookup_lt_is_Some_1. eauto. }
      rewrite turn_ctx_incr_pop; done. }
    simpl.
    iDestruct "H" as "[#Hi Hctx]".
    iDestruct (turn_ctx_incr_pop_eq with "Hctx") as "[Hctx Hturn]"; first done.
    iAssert (SEQinv γl q (popTicket `mod` q) (MkSeq γ v) (popTicket + 1) pushTicket)%I with "[Hi Hctx]" as "Hsingl".
    { iFrame "#∗". }
    iCombine "Hsingl Hs" as "Hs".
    iDestruct (big_sepL_delete' _ SEQs (popTicket `mod` q)) as "HI"; first done.
    iDestruct ("HI" with "Hs") as "HOHO".
    by iFrame "#∗".
  Qed.

  Lemma SEQs_incr_pop γl q SEQs popTicket pushTicket :
    0 < q →
    SEQsinv γl q SEQs popTicket pushTicket ==∗
    ∃ (γ : gname) v,
      let i := (popTicket `mod` q) in
      ⌜SEQs !! i = Some (MkSeq γ v)⌝ ∗
      isSEQ γ (R γl q i) v ∗
      SEQsinv γl q SEQs (popTicket + 1) pushTicket ∗
      dequeue_turn γ (popTicket / q).
  Proof.
    iIntros (Hlt) "Hinv".
    iAssert (⌜length SEQs = q⌝%I) as %Hlen.
    { by iDestruct "Hinv" as "[$ _]". }
    set (i := popTicket `mod` q).
    assert (i < length SEQs) as Hlt'; first lia.
    destruct (lookup_lt_is_Some_2 _ _ Hlt') as [[γ v] Hlook].
    iExists γ, v.
    iModIntro.
    iSplit; first done.
    rewrite /SEQsinv.
    by iDestruct (SEQs_inc_prop_go with "Hinv") as "Hinv".
  Qed.

  (* If you increment pushTicket you get a turn. You also get the persistent
  predicate for the SEQer b.c. otherwise the turn is not useful. *)
  Lemma SEQs_incr_push γl q SEQs popTicket pushTicket :
    0 < q →
    SEQsinv γl q SEQs popTicket pushTicket ==∗
    ∃ (γ : gname) v,
      let i := (pushTicket `mod` q) in
      ⌜SEQs !! i = Some (MkSeq γ v)⌝ ∗
      isSEQ γ (R γl q i) v ∗
      SEQsinv γl q SEQs popTicket (pushTicket + 1) ∗
      enqueue_turn γ (pushTicket / q).
  Proof.
    iIntros (H0q) "[%Hlen HInv]".
    pose (i := pushTicket `mod` q).
    assert (i < length SEQs) as Hi by lia.
    apply lookup_lt_is_Some_2 in Hi. destruct Hi as [[γ v] Hi].
    iExists γ,v.
    rewrite (big_sepL_delete _ _ i); last done.
    iDestruct "HInv" as "[Hi HInv]".
    (* First, update the queues that are *not* affected, i.e. all the non-i queues *)
    rewrite (big_sepL_mono _ (fun j sq => ⌜j ≠ i⌝ → SEQinv γl q j sq popTicket (pushTicket+1))%I); last first.
    { iIntros (k [v' γ'] Hk) "Hq".
      iIntros (Hki). destruct (decide (k = i)); first (simplify_eq/=); [].
      unfold SEQinv.
      destruct (decide (k < i)).
      + iDestruct "Hq" as "[$ Hq]".
        rewrite turn_ctx_incr_push; eauto. lia.
      + assert (i < k) by lia.
        iDestruct "Hq" as "[$ Hq]".
        assert (k < q).
        { rewrite -Hlen. apply lookup_lt_is_Some_1. eauto. }
        rewrite turn_ctx_incr_push; eauto. }
    (* Update the resources for the i-th queue and obtain the ticket *)
    iAssert (|==> SEQinv γl q i {| seq_val := v; seq_gname := γ |} popTicket (pushTicket+1) ∗ enqueue_turn γ (pushTicket `div` q))%I with "[Hi]" as ">[Hi $]".
    { iDestruct "Hi" as "[#Hinv Htctx]".
      rewrite /SEQinv. iFrame "Hinv".
      rewrite turn_ctx_incr_push_eq; eauto. }
    iModIntro. repeat (iSplitR; first done).
    iDestruct "Hi" as "[#$ H2]".
    rewrite /SEQsinv. iSplit; first done.
    iApply big_sepL_delete'; eauto. rewrite /SEQinv. by iFrame.
  Qed.

  (* The i'th enqueue/push must add this to the invariant. *)
  Definition push_i A γl γt γm i : iProp Σ :=
    token γt i ∨
    (∃ id v vₛ, own γm (◯ {[ i := to_agree id ]}) ∗
                (refines_right id (of_val vₛ)) ∗
                A v vₛ ∗
                ghost_list_pointsto γl i v).

  Definition mpmcInv A γt γm γl q (ℓpop ℓpush ℓarr : loc) (SEQs : list seq)
    (xsᵢ : list val) (ℓs : loc) (lk : val) : iProp Σ :=
    ∃ (popTicket pushTicket : nat) (m : list val) (p : Qp) threads,

      (* The physical state. *)
      ℓpop ↦ #popTicket ∗
      ℓpush ↦ #pushTicket ∗
      ℓarr ↦∗{#p} (seq_val <$> SEQs) ∗ (* FIXME: Use persistent points-to predicate here. *)

      (* Ghost list *)
      (ghost_list γl m ∗
      ⌜length m = pushTicket⌝ ∗
      ⌜drop popTicket m = xsᵢ⌝) ∗

      (* Knowledge about each SEQ. *)
      SEQsinv γl q SEQs popTicket pushTicket ∗

      (* Handling of external LP. *)
      (* The 'I-came-first' token *)
      tokens_from γt (popTicket `max` pushTicket) ∗ (* Keeps track of which tokens we own. *)
      (* Some pop operations has decided on a [j] and a [K]. *)
      own γm (● threads) ∗
      ⌜dom threads ⊆ set_seq 0 popTicket⌝ ∗
      (* Every push operation must show this for i. *)
      ([∗ set] i ∈ (set_seq 0 pushTicket), push_i A γl γt γm i) ∗
      (* When popTicket is greater than pushTicket the pop operation has left a
        spec thread resource. *)
      ([∗ set] i ∈ (set_seq pushTicket (popTicket - pushTicket)),
        ∃ id, own γm (◯ {[ i := to_agree id ]}) ∗ (refines_right id (CG_dequeue lk #ℓs #()))).

  Definition I A γt γm γl q ℓpop ℓpush ℓarr SEQs ℓs lk : iProp Σ :=
    (∃ xsᵢ xsₛ,
      mpmcInv A γt γm γl q ℓpop ℓpush ℓarr SEQs xsᵢ ℓs lk ∗
      cgQueueInv ℓs lk xsₛ ∗
      [∗ list] xᵢ ; xₛ ∈ xsᵢ ; xsₛ, A xᵢ xₛ)%I.

  (* Decide j and K. *)
  Lemma thread_alloc (γm : gname) mt popTicket (id : ref_id) :
    dom mt ⊆ set_seq 0 popTicket →
    own γm (● mt) ==∗
    ⌜dom (<[ popTicket := to_agree id ]>mt) ⊆ set_seq 0 (popTicket + 1)⌝ ∗
    own γm (● (<[ popTicket := to_agree id ]>mt)) ∗
    own γm (◯ ({[ popTicket := to_agree id ]})).
  Proof.
    iIntros (Hsub) "Hown".
    iMod (own_update with "Hown") as "[Hown Hfrag]".
    { apply auth_update_alloc.
      eapply (alloc_local_update _ _ popTicket (to_agree (id : ref_idO))); last done.
      apply not_elem_of_dom.
      set_solver by lia. }
    iModIntro. iFrame.
    iPureIntro. rewrite dom_insert. set_solver by lia.
  Qed.

  Lemma push_i_add A γl γt γm n :
    ([∗ set] i ∈ set_seq 0 n, push_i A γl γt γm i)
    -∗ push_i A γl γt γm n
    -∗ ([∗ set] i ∈ set_seq 0 (n + 1), push_i A γl γt γm i).
  Proof.
    iIntros "Ho Htok".
    rewrite Nat.add_1_r.
    rewrite set_seq_S_end_union_L. simpl.
    iApply big_sepS_insert; first set_solver by lia.
    iSplitL "Htok"; iFrame.
  Qed.


  Lemma makeArray_newSQueue (γl : gname) (q : nat) :
    {{{ ⌜q > 0⌝ }}}
      array_init #q newSQueue
    {{{ ℓarr SEQs, RET #ℓarr;
      ⌜length SEQs = q⌝ ∗
      ℓarr ↦∗ (seq_val <$> SEQs) ∗
      ([∗ list] i ↦ s ∈ SEQs, SEQinv γl q i s 0 0)
    }}}.
  Proof.
    iIntros (ϕ) "%Hqgt Hϕ".
    iApply (wp_array_init_fmap seq_val (λ i s, SEQinv γl q i s 0 0)); first lia.
    { iApply big_sepL_intro. iModIntro.
      iIntros (k i Hi).
      wp_apply newSEQ_spec; first done.
      iIntros (γ v) "(isSEQ & Ht1 & Ht2)".
      iExists (MkSeq γ v). iSplit; first done.
      rewrite /SEQinv.
      rewrite (turn_ctx_initial _ q). by iFrame. }
    iNext.
    iIntros (ℓarr SEQs) "(%Hlen & arrPts & Hlist)".
    iApply "Hϕ".
    iFrame. iPureIntro. by simplify_eq/=.
  Qed.


  Lemma big_sepS_take_first (n m : nat) (Φ : nat → iProp Σ) :
    0 < m → ([∗ set] i ∈ set_seq n m, Φ i) -∗ Φ n ∗ ([∗ set] i ∈ set_seq (n + 1) (m - 1), Φ i).
  Proof.
    intros Hlt.
    rewrite (set_seq_take_start_L n m 1); last lia.
    rewrite big_sepS_union; last set_solver by lia.
    simpl.
    assert ({[n]} ∪ ∅ = {[n]}) as ->; first by set_solver.
    rewrite big_sepS_singleton.
    auto.
  Qed.

  Lemma enqueue_refinement (A : lrel Σ) (q : nat) γt γm γl ℓpop ℓpush ℓarr SEQs list l x x' :
    q > 0 →
    inv queueN (I A γt γm γl q ℓpop ℓpush ℓarr SEQs list l) -∗
    A x x' -∗
    REL enqueue #ℓarr #q #ℓpush x << CG_enqueue l #list x' : ().
  Proof.
    iIntros (?) "#Hinv #HA".
    rel_rec_l.
    rel_pures_l.

    (* This is the linearization points for enqueue. *)
    rel_apply_l refines_faa_l.
    iInv queueN as (xs xsₛ) "(Hmpmc & Hsq & Hlink)" "Hcl".
    iDestruct "Hmpmc" as (popTicket pushTicket m p mt)
                           "(>popPts & >pushPts & >[arrPts arrPts'] & >(Hlist & %Hlen & %Hlisteq) & Hseqs & HAtok & Ha & Hb & Hpush & Hmore)".
    iModIntro. iExists _. iFrame "pushPts". iNext. iIntros "pushPts".

    (* We need to get a ticket out for the SEQ. *)
    iMod (SEQs_incr_push with "Hseqs") as (γ v) "(%Hattss & #HisSEq & Hseqs & Hturn)"; first lia.

    (* This is the linearization point for enqueue. *)
    rel_apply_r (refines_CG_enqueue_r with "Hsq"). iIntros "Hsq".

    (* We insert the enqueued element into the logical list. *)
    iMod (ghost_list_append _ _ x with "Hlist") as "[Hlist #Helem]".

    (* Did we came first or did a pop come before us? *)
    destruct (le_lt_dec popTicket pushTicket) as [Hle|Hgt].

    * (* We came first *)

      (* In this case handling the LP/token infrastructure is fiarly
        straightforward. Since [popTicket ≤ pushTicket] we can take a ticket. *)
      rewrite (max_r _ _ Hle).
      iDestruct (tokens_take with "HAtok") as "[HAtok Htok]".
      iDestruct (push_i_add with "Hpush [$]") as "Hpush".

      iMod ("Hcl" with "[-arrPts Hturn]") as "_".
      { iNext. iExists (xs ++ [x]), (xsₛ ++ [x']).
        iFrame. iFrame "HA".
        rewrite big_sepL2_nil.
        iSplitL; last done.
        iExists popTicket, (pushTicket + 1), _, _, _.
        assert ((pushTicket + 1)%Z = (pushTicket + 1)%nat) as -> by lia.
        assert (popTicket `max` (pushTicket + 1) = pushTicket + 1) as -> by lia.
        assert (popTicket - (pushTicket + 1) = 0) as -> by lia.
        iFrame. simpl.
        rewrite big_sepS_empty.
        iPureIntro. split; last done. split.
        { rewrite app_length. simpl. lia. }
        rewrite drop_app_le; last lia.
        rewrite Hlisteq. done. }
      rel_pures_l.
      rel_bind_l (! _)%E.
      rel_apply_l refines_wp_l.
      assert ((Z.of_nat pushTicket `rem` Z.of_nat q)%Z = Z.of_nat (pushTicket `mod` q)) as ->.
      { rewrite Nat2Z.inj_mod. apply Z.rem_mod_nonneg; lia. }
      wp_apply (wp_load_offset with "arrPts").
      { rewrite list_lookup_fmap. rewrite Hattss. reflexivity. }
      iIntros "arrPts".
      rewrite Z.quot_div_nonneg; [|lia|lia].
      rewrite -Nat2Z.inj_div.
      rel_apply_l refines_wp_l.
      wp_apply (enqueueWithTicket_spec' _ (R _ q (pushTicket `mod` q)) with "[-]").
      2: { iIntros. rel_values. }
      iFrame "Hturn".
      rewrite /R.
      rewrite div_mod'; last lia.
      rewrite Hlen.
      iFrame "#".

    * (* We came _last_ and we must step forward a dequeue. *)

      (* The queue is empty. *)
      assert (length xs = 0) as Hlen'.
      { rewrite -Hlisteq. rewrite drop_ge; [done|lia]. }
      destruct xs as [|? ?]; last done.
      iDestruct (big_sepL2_nil_inv_l with "Hlink") as %->.

      iDestruct (big_sepS_take_first with "Hmore") as "[Hobl Hmore]"; first lia.
      iDestruct "Hobl" as (id) "[#Hagree Hj]".
      simpl.

      (* We already carried out the LP for enqueue, we now also perform the LP
           for the dequeue. *)
      iMod (refines_right_CG_dequeue with "Hsq Hj") as "[Hsq Hj]".
      { solve_ndisj. }

      (* We have now carried out our obligation to the dequeue and can prove that. *)
      rewrite Hlen.
      iDestruct (push_i_add with "Hpush [Hj]") as "Hpush".
      { iRight. iExists id, _, _. iFrame "#∗". }

      iMod ("Hcl" with "[-arrPts Hturn]") as "_".
      { iNext. iExists [], []. iFrame "Hsq".
        simpl. iSplitL; last done.
        iExists popTicket, (pushTicket + 1), _, _, _.
        assert ((pushTicket + 1)%Z = (pushTicket + 1)%nat) as -> by lia.
        assert (popTicket - (pushTicket + 1) = popTicket - pushTicket - 1) as -> by lia.
        assert (popTicket `max` (pushTicket + 1) = popTicket `max` pushTicket) as -> by lia.
        simpl. iFrame.
        iPureIntro. split.
        - rewrite app_length. simpl. lia.
        - apply drop_ge. rewrite app_length. simpl. lia. }

      rel_pures_l.
      rel_bind_l (! _)%E.
      rel_apply_l refines_wp_l.
      assert ((Z.of_nat pushTicket `rem` Z.of_nat q)%Z = Z.of_nat (pushTicket `mod` q)) as ->.
      { rewrite Nat2Z.inj_mod. apply Z.rem_mod_nonneg; lia. }
      wp_apply (wp_load_offset with "arrPts").
      { rewrite list_lookup_fmap. rewrite Hattss. reflexivity. }
      iIntros "arrPts".
      rewrite Z.quot_div_nonneg; [|lia|lia].
      rewrite -Nat2Z.inj_div.
      rel_apply_l refines_wp_l.
      wp_apply (enqueueWithTicket_spec' _ (R _ q (pushTicket `mod` q)) with "[-]").
      2: { iIntros. rel_values. }
      iFrame "Hturn".
      rewrite /R.
      rewrite div_mod'; last lia.
      iFrame "#".
  Qed.

  Lemma dequeue_refinement (A : lrel Σ) (q : nat) γt γm γl ℓpop ℓpush ℓarr SEQs list l :
    q > 0 →
    inv queueN (I A γt γm γl q ℓpop ℓpush ℓarr SEQs list l) -∗
    REL dequeue #ℓarr #q #ℓpop << CG_dequeue l #list #() : A.
  Proof.
    iIntros (?) "#Hinv".
    rel_rec_l.
    rel_pures_l.

    (* We get to the FAA which increments the popTicket. *)
    rel_apply_l refines_faa_l.
    iInv queueN as (xs xsₛ) "(Hmpmc & Hsq & Hlink)" "Hcl".
    iDestruct "Hmpmc" as (popTicket pushTicket m p mt)
      "(>popPts & >pushPts & >[arrPts arrPts'] & >(Hlist & %Hlen & %Hlisteq) & Hseqs & HAtok & Ha & >%Hb & Hpush & Hmore)".
    iModIntro. iExists _. iFrame "popPts". iNext. iIntros "popPts".

    (* We need to get a ticket out for the SEQ. *)
    iMod (SEQs_incr_pop with "Hseqs") as (γ v) "(%Hattss & #HisSEq & Hseqs & Hturn)"; first done.

    (* Did we came first or did a push come before us? *)
    destruct (le_lt_dec pushTicket popTicket) as [Hle|Hgt].

    * (* We came first and there is currently no element for us. *)

      (* We can take the I-came-first-token. *)
      iDestruct (tokens_take with "HAtok") as "[HAtok Htok]".
      replace (popTicket `max` pushTicket) with popTicket by lia.
      iApply refines_split.
      iIntros (id) "Hright".
      (* We now allocate the [id] agreement. *)
      iMod (thread_alloc _ _ _ id with "Ha") as "(%Sub & Ha & #Hdec)"; first done.

      assert (length xs = 0) as Hlen'.
      { rewrite -Hlisteq. rewrite drop_ge; [done|lia]. }
      destruct xs as [|? ?]; last done.
      iDestruct (big_sepL2_nil_inv_l with "Hlink") as %->.
      simpl.

      iMod ("Hcl" with "[-arrPts Hturn Htok]") as "_".
      { iNext. iExists [], []. simpl. iFrame.
        iExists (popTicket + 1), pushTicket, _, _, _.
        simpl.
        assert ((popTicket + 1)%Z = (popTicket + 1)%nat) as ->; first lia.
        replace ((popTicket + 1) `max` pushTicket) with (popTicket + 1) by lia.
        (* assert (popTicket `max` pushTicket + 1 = (popTicket + 1) `max` pushTicket) as ->; first lia. *)
        iFrame.
        repeat iSplit; eauto with lia.
        { iPureIntro. apply drop_ge. lia. }
        replace (popTicket + 1 - pushTicket) with (S (popTicket - pushTicket)) by lia.
        rewrite set_seq_S_end_union_L.
        rewrite big_sepS_union; last set_solver by lia.
        iFrame.
        rewrite big_sepS_singleton.
        iExists id. iFrame.
        replace (pushTicket + (popTicket - pushTicket)) with popTicket by lia.
        iFrame "#". }
      (* FIXME: The the iModIntro here unfolds [refines_left]. *)
      (* iModIntro. *)
      rel_pures_l.

      assert ((Z.of_nat popTicket `rem` Z.of_nat q)%Z = Z.of_nat (popTicket `mod` q)) as ->.
      { rewrite Nat2Z.inj_mod. apply Z.rem_mod_nonneg; lia. }
      rel_apply_l refines_wp_l.
      wp_apply (wp_load_offset with "arrPts").
      { rewrite list_lookup_fmap. rewrite Hattss. reflexivity. }
      iIntros "arrPts".

      rewrite Z.quot_div_nonneg; [|lia|lia].
      rewrite -Nat2Z.inj_div.
      iApply wp_fupd.
      simpl.
      wp_apply (dequeueWithTicket_spec2 _ (R _ q (popTicket `mod` q)) with "[-Htok]").
      { iFrame "#∗". }
      iIntros (?).
      rewrite /R.
      rewrite div_mod'; last lia.
      iIntros "#Hag".

      clear.
      (* We now open the invariant again. It this point we can be sure that a
           enqueue operation has stepped our specification forward. *)
      iInv queueN as (xs xsₛ) "(Hmpmc & Hsq & Hlink)" "Hcl".
      iDestruct "Hmpmc" as (popTicket' pushTicket m p mt)
                             "(>popPts & >pushPts & >[arrPts arrPts'] & (>Hlist & >%Hlen & Hlisteq) & Hseqs & HAtok & Ha & Hb & Hpush & Hmore)".
      (* We now "flip" the disjunction for one of the popTickets. *)
      iDestruct (ghost_list_le with "Hlist Hag") as %popLePush.
      rewrite (big_sepS_delete _ _ popTicket). 2: { rewrite elem_of_set_seq. lia. }
      iDestruct "Hpush" as "[[>Htok'|Hright] Hpush]".
      { by iCombine "Htok Htok'" gives %Hv%set_singleton_invalid. }
      iDestruct "Hright" as (id' v' vₛ) "(>#Hdec' & Hright & #Hrel & >#Hag')".
      iAssert (push_i A γl γt γm popTicket) with "[Htok]" as "Hi".
      { iLeft. iFrame. }

      iMod ("Hcl" with "[-Hright]") as "_".
      { iNext. iExists xs, xsₛ. iFrame.
        iCombine "Hi Hpush" as "Hpush".
        rewrite -big_sepS_insert; last set_solver by lia.
        (* rewrite difference_union_distr_l_L. *)
        replace ({[popTicket]} ∪ set_seq 0 pushTicket ∖ {[popTicket]}) with (set_seq (C:=gset nat) 0 pushTicket) by set_solver by lia.
        iExists _, _, _, _, _. by iFrame. }

      iModIntro. iNext. iModIntro.
      iDestruct (map_list_agree with "Hag Hag'") as %->.
      iDestruct (decide_agree with "Hdec Hdec'") as %->.
      iApply refines_combine; last iApply "Hright".
      rel_values.

    * (* An enqueue has been here. *)
      (* We can take a logical value from the list. *)
      (* The list must be non-empty. *)
      assert (is_Some (m !! popTicket)) as [x' Hlk].
      { apply lookup_lt_is_Some_2. lia. }
      destruct xs as [|x xs]. {
        erewrite drop_S in Hlisteq; last apply Hlk.
        discriminate. }
      clear x' Hlk.
      epose proof (drop_nth _ _ _ _ Hlisteq) as HMlook.
      iMod (ghost_list_lookup with "Hlist") as "[Hlist #Hlistelem]".
      { done. }
      iDestruct (big_sepL2_cons_inv_l with "Hlink") as (xₛ xsₛ' ->) "[#Hrel Hlink]".

      (* In this case handling the LP/token infrastructure is fiarly
        straightforward. The tickets don't change. *)
      assert (popTicket `max` pushTicket = (popTicket + 1) `max` pushTicket) as -> by lia.

      (* Step specification forward. *)
      rel_apply_r (refines_CG_dequeue_cons_r with "Hsq"). iIntros "Hsq".

      (* Close the invariant. *)
      iMod ("Hcl" with "[-arrPts Hturn]") as "_".
      { iNext. iExists xs, xsₛ'. iFrame.
        iExists (popTicket + 1), pushTicket, _, _, _.
        assert ((popTicket + 1)%Z = (popTicket + 1)%nat) as -> by lia.
        assert (popTicket + 1 - pushTicket = 0) as -> by lia.
        iFrame.
        rewrite big_sepS_empty.
        repeat iSplit; try by (iPureIntro; set_solver by lia).
        iPureIntro.
        rewrite Nat.add_1_r .
        pose proof (drop_S _ _ _ HMlook) as T.
        rewrite T in Hlisteq.
        pose proof Hlisteq as [= ?].
        done. }
      rel_pures_l.

      rel_bind_l (! _)%E.
      rel_apply_l refines_wp_l.
      assert ((Z.of_nat popTicket `rem` Z.of_nat q)%Z = Z.of_nat (popTicket `mod` q)) as ->.
      { rewrite Nat2Z.inj_mod. apply Z.rem_mod_nonneg; lia. }
      wp_apply (wp_load_offset with "arrPts").
      { rewrite list_lookup_fmap. rewrite Hattss. reflexivity. }
      iIntros "arrPts".

      rewrite Z.quot_div_nonneg; [|lia|lia].
      rewrite -Nat2Z.inj_div.
      rel_apply_l refines_wp_l.
      wp_apply (dequeueWithTicket_spec' _ (R _ q (popTicket `mod` q)) with "[-]").
      { iFrame "#∗". }
      iIntros (?).
      rewrite /R.
      rewrite Nat.mul_comm.
      rewrite <- (Nat.div_mod _ q); last lia.
      iIntros "Hlistelem'".
      iDestruct (map_list_agree with "Hlistelem Hlistelem'") as %<-.
      rel_values.
  Qed.

  Lemma queue_refinement (q : nat) :
    q > 0 →
    ⊢ REL newQueue #q << CG_queue : ∀ A, (A → ()) * (() → A).
  Proof.
    intros Hqgt.

    rel_rec_l. rel_pure_l.
    iApply refines_forall.
    iModIntro.
    iIntros (A).

    iMod ghost_list_alloc as (γl) "Hlist".

    (* Step through implementation. *)
    rel_bind_l (array_init _ _).
    rel_apply_l refines_wp_l.
    wp_apply (makeArray_newSQueue γl); first done.
    iIntros (ℓarr SEQs) "(%Htsslen & arrPts & Hseqs)".
    rel_alloc_l ℓpush as "pushts".
    rel_alloc_l ℓpop as "popPts".
    do 2 rel_pure_l.

    (* Step through specification. *)
    rel_alloc_r list as "listPts".
    rel_pure_r.
    rel_pure_r.
    rel_apply_r refines_newlock_r. iIntros (l) "lofal".
    do 2 rel_pure_r.

    (* Establish the invariant. *)
    iMod (own_alloc (set_above 0)) as (γt) "Htok"; first done.
    iMod (own_alloc (● ∅ : requestRegR)) as (γm) "Hdec"; first by apply auth_auth_valid.
    iMod (inv_alloc queueN _ (I A γt γm γl q ℓpop ℓpush ℓarr SEQs _ _) with "[-]") as "#Hinv".
    { iNext. iExists [], []. simpl. iFrame. iExists 0, 0, ∅, 1%Qp, ∅. cbn. iFrame.
      rewrite !dom_empty_L !big_sepS_empty. iFrame. done. }

    iApply refines_pair.
    - (* enqueue *)
      rel_pures_l.
      rel_pures_r.
      iApply refines_arrow_val. iModIntro.
      iIntros (x x') "#Hrel".
      rel_pures_l. rel_rec_r.
      by iApply enqueue_refinement.
    - (* dequeue *)
      rel_pures_l.
      rel_pures_r.
      iApply refines_arrow_val. iModIntro.
      iIntros (?? [-> ->]).
      rel_pures_l.
      rel_pures_r.
      by iApply dequeue_refinement.
  Qed.

End queue_refinement.
