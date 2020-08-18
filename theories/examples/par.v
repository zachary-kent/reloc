(** THIS EXAMPLE IS WIP *)
From iris.algebra Require Import excl.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib Require Export spawn par.
From reloc Require Export reloc lib.Y (* for bot *).

(**
Axioms/rules for parallel composition

- [x] par is commutative
    requires unfolding
- [x] () is a unit
- [x] e1 ;; e2 << (e1 ||| e2)
    also requires unfolding
- [x] interchange law
    also requires unfolding
*)

Notation "e1 ∥ e2" := (((e1;; #()) ||| (e2;; #()));; #())%E
                        (at level 60) : expr_scope.
(* Notation "e1 ∥ e2" := (((e1;; #()) ||| (e2;; #()))%V;; #()) *)
(*                         (at level 60) : val_scope. *)


Section rules.
  Context `{!relocG Σ, !spawnG Σ}.

  Lemma par_l_2 e1 e2 t :
    (WP e1 {{ _, True }}) -∗
    (REL e2 << t : ()) -∗
    REL (e1 ∥ e2) << t : ().
  Proof.
    iIntros "He1 He2".
    rel_pures_l. rel_rec_l.
    rel_pures_l. rel_bind_l (spawn _).
    iApply refines_wp_l.
    pose (N:=nroot.@"par").
    iApply (spawn_spec N (λ _, True)%I with "[He1]").
    - wp_pures. wp_bind e1. iApply (wp_wand with "He1").
      iIntros (?)  "_"; by wp_pures.
    - iNext. iIntros (l) "hndl". iSimpl.
      rel_pures_l. rel_bind_l e2. rel_bind_r t.
      iApply (refines_bind with "He2").
      iIntros (? ?) "[% %]"; simplify_eq/=.
      rel_pures_l.
      rel_bind_l (spawn.join _).
      iApply refines_wp_l.
      iApply (join_spec with "hndl").
      iNext. iIntros (?) "_". simpl.
      rel_pures_l. by rel_values.
  Qed.

  Lemma par_l_2' Q K e1 e2 t :
    (WP e1 {{ _, Q }}) -∗
    (REL e2 << t : ()) -∗
    (Q -∗ REL #() << fill K (#() : expr) : ()) -∗
    REL (e1 ∥ e2) << fill K t : ().
  Proof.
    iIntros "He1 He2 Ht".
    rel_pures_l. rel_rec_l.
    rel_pures_l. rel_bind_l (spawn _).
    iApply refines_wp_l.
    pose (N:=nroot.@"par").
    iApply (spawn_spec N (λ _, Q)%I with "[He1]").
    - wp_pures. wp_bind e1. iApply (wp_wand with "He1").
      iIntros (?)  "HQ"; by wp_pures.
    - iNext. iIntros (l) "hndl". iSimpl.
      rel_pures_l. rel_bind_l e2.
      iApply (refines_bind with "He2").
      iIntros (? ?) "[% %]"; simplify_eq/=.
      rel_pures_l.
      rel_bind_l (spawn.join _).
      iApply refines_wp_l.
      iApply (join_spec with "hndl").
      iNext. iIntros (?) "HQ". simpl.
      rel_pures_l. by iApply "Ht".
  Qed.

  Lemma par_l_1 e1 e2 t :
    (REL e1 << t : ()) -∗
    (WP e2 {{ _, True }}) -∗
    REL (e1 ∥ e2) << t : ().
  Proof.
    iIntros "He1 He2".
    rel_pures_l. rel_rec_l.
    rel_pures_l.
    pose (N:=nroot.@"par").
    rewrite refines_eq /refines_def. iIntros (j K) "#Hspec Hj".
    iModIntro. wp_bind (spawn _).
    iApply (spawn_spec N (λ _, j ⤇ fill K #())%I with "[He1 Hj]").
    - wp_pures. wp_bind e1.
      iMod ("He1" with "Hspec Hj") as "He1".
      iApply (wp_wand with "He1").
      iIntros (?)  "P". wp_pures.
      by iDestruct "P" as (v') "[Hj [-> ->]]".
    - iNext. iIntros (l) "hndl". iSimpl.
      wp_pures. wp_bind e2.
      iApply (wp_wand with "He2"). iIntros (?) "_".
      wp_pures.
      wp_apply (join_spec with "hndl").
      iIntros (?) "Hj". wp_pures. iExists #(). eauto with iFrame.
  Qed.

  Lemma par_l_1' Q K e1 e2 t :
    (REL e1 << t : ()) -∗
    (WP e2 {{ _, Q }}) -∗
    (Q -∗ REL #() << fill K (#() : expr) : ()) -∗
    REL (e1 ∥ e2) << fill K t : ().
  Proof.
    iIntros "He1 He2 Ht".
    rel_pures_l. rel_rec_l.
    rel_pures_l.
    pose (N:=nroot.@"par").
    rewrite {1 3}refines_eq /refines_def. iIntros (j K') "#Hspec Hj".
    iModIntro. wp_bind (spawn _).
    iApply (spawn_spec N (λ _, j ⤇ fill (K++K') #())%I with "[He1 Hj]").
    - wp_pures. wp_bind e1.
      rewrite -fill_app.
      iMod ("He1" with "Hspec Hj") as "He1".
      iApply (wp_wand with "He1").
      iIntros (?)  "P". wp_pures.
      by iDestruct "P" as (v') "[Hj [-> ->]]".
    - iNext. iIntros (l) "hndl". iSimpl.
      wp_pures. wp_bind e2.
      iApply (wp_wand with "He2"). iIntros (?) "HQ".
      wp_pures.
      wp_apply (join_spec with "hndl").
      iIntros (?) "Hj".
      iSpecialize ("Ht" with "HQ").
      rewrite refines_eq /refines_def.
      rewrite fill_app.
      iMod ("Ht" with "Hspec Hj") as "Ht".
      rewrite wp_value_inv. iMod "Ht" as (?) "[Ht [_ ->]]".
      wp_pures. iExists #(). eauto with iFrame.
  Qed.

  (* Lemma par_r_1 e1 e2 t (A : lrel Σ) E : *)
  (*   ↑ relocN ⊆ E → *)
  (*   is_closed_expr [] e1 → *)
  (*   (∀ i C, i ⤇ fill C e1 ={E}=∗ ∃ (v : val), *)
  (*           i ⤇ fill C v ∗ REL t << (v, e2) @ E : A) -∗ *)
  (*   REL t << (e1 ||| e2)%V @ E : A. *)
  (* Proof. *)
  (*   iIntros (??) "H". *)
  (*   rel_rec_r. repeat rel_pure_r. *)
  (*   rel_rec_r. *)
  (*   repeat rel_pure_r. rel_alloc_r c2 as "Hc2". *)
  (*   repeat rel_pure_r. rel_fork_r i as "Hi". *)
  (*   { simpl. eauto. } *)
  (*   repeat rel_pure_r. *)
  (*   tp_rec i. simpl. *)
  (*   tp_bind i e1. *)
  (*   iMod ("H" with "Hi") as (v1) "[Hi H]". *)
  (*   iSimpl in "Hi". tp_pure i (InjR v1). tp_store i. *)
  (* Abort. *)
  (*   (* rewrite refines_eq /refines_def. *) *)
  (*   (* iIntros (ρ') "_". clear ρ'. *) *)
  (*   (* iIntros (j K) "Hj". *) *)
  (*   (* tp_bind j e2. *) *)

  (* this one we can prove without unfolding *)
  Lemma par_unit_1 e :
    (REL e << e : ()) -∗
    REL (#() ∥ e) << e : ().
  Proof.
    iIntros "He".
    iApply (par_l_2 with "[] He").
    by iApply wp_value.
  Qed.
  Lemma par_unit_2 e :
    (REL e << e : ()) -∗
    REL e << (#() ∥ e) : ().
  Proof.
    iIntros "He".
    rel_pures_r. rel_rec_r. rel_pures_r. rel_rec_r.
    rel_pures_r. rel_alloc_r c2 as "Hc2".
    rel_pures_r. rel_fork_r i as "Hi".
    rel_pures_r.
    tp_rec i. simpl.
    tp_pures i. tp_store i.
    rel_bind_l e. rel_bind_r e.
    iApply (refines_bind with "He").
    iIntros (v v') "[-> ->]".
    simpl. rel_pures_r.
    rel_rec_r. rel_load_r. rel_pures_r.
    rel_values.
  Qed.

  (* This proof is now simpler but it still requires unfolding the REL judgement *)
  Lemma par_comm e1 e2 :
    is_closed_expr [] e1 →
    is_closed_expr [] e2 →
    (REL e1 << e1 : ()) -∗
    (REL e2 << e2 : ()) -∗
    REL (e2 ∥ e1) << (e1 ∥ e2) : ().
  Proof.
    iIntros (??) "He1 He2". rel_pures_r.
    rel_rec_r. rel_pures_r. rel_rec_r.
    rel_pures_r. rel_alloc_r c2 as "Hc2".
    rel_pures_r. rel_fork_r i as "Hi".
    { simpl. eauto. }
    tp_pure i (App _ _). simpl.
    rel_pures_r.
    rel_bind_r e2.
    iApply refines_spec_ctx. iIntros "#Hs".
    iApply (par_l_1' (i ⤇ (#c2 <- InjR (#();; #())))%I
              with "He2 [He1 Hi]").
    { rewrite refines_eq /refines_def.
      tp_bind i e1.
      iMod ("He1" with "Hs Hi") as "He1". simpl.
      iApply (wp_wand with "He1"). iIntros (?).
      iDestruct 1 as (?) "[Hi [-> ->]]". done. }
    iIntros "Hi". simpl. rel_pures_r.
    tp_pures i. tp_store i.
    rel_rec_r. rel_load_r. rel_pures_r. rel_values.
  Qed.

  Lemma par_bot_2 e1 :
    ⊢ REL bot #() << e1 ∥ bot #() : ().
  Proof. rel_apply_l bot_l. Qed.

  Lemma par_bot_1 e1 :
    (WP e1 {{_ , True}}) -∗ (* TODO: what can we do about this assignment? *)
    REL (e1 ∥ bot #()) << bot #() : ().
  Proof.
    iIntros "He1".
    iApply (par_l_2 with "He1").
    rel_apply_l bot_l.
  Qed.

  Lemma seq_par e1 e2 (A B : lrel Σ) :
    is_closed_expr [] e1 →
    is_closed_expr [] e2 →
    (REL e1 << e1 : A) -∗
    (REL e2 << e2 : B) -∗
    REL e1 ;; e2 << (e1 ||| e2)%V : lrel_true.
  Proof.
    iIntros (??) "He1 He2". rel_rec_r. repeat rel_pure_r.
    rel_rec_r.
    repeat rel_pure_r. rel_alloc_r c2 as "Hc2".
    repeat rel_pure_r. rel_fork_r i as "Hi".
    { simpl. eauto. }
    repeat rel_pure_r.
    tp_rec i. simpl.
    rewrite {3}refines_eq /refines_def.
    iIntros (j K) "#Hs Hj". iModIntro.
    tp_bind j e2. tp_bind i e1.
    (* execute e1 *)
    wp_bind e1. tp_bind i e1.
    rewrite {1}refines_eq /refines_def.
    iMod ("He1" with "Hs Hi") as "He1".
    iApply (wp_wand with "He1"). iIntros (v1).
    iDestruct 1 as (v2) "[Hi Hv]". wp_pures.
    (* execute e2 *)
    rewrite refines_eq /refines_def.
    iMod ("He2" with "Hs Hj") as "He2".
    iApply wp_fupd.
    iApply (wp_wand with "He2"). iIntros (w1).
    iDestruct 1 as (w2) "[Hj Hw]".
    iSimpl in "Hi". iSimpl in "Hj".
    tp_pure i _.
    tp_store i.
    tp_pures j. tp_rec j.
    tp_load j.
    tp_pures j.
    iModIntro. iExists _. iFrame.
  Qed.

  Lemma interchange a b c d (A B C D : lrel Σ) :
    is_closed_expr [] a →
    is_closed_expr [] b →
    is_closed_expr [] c →
    is_closed_expr [] d →
    (REL a << a : A) -∗
    (REL b << b : B) -∗
    (REL c << c : C) -∗
    (REL d << d : D) -∗
    REL (a ||| b)%V ;; (c ||| d)%V << ((b ;; c) ||| (a ;; d))%V : lrel_true.
  Proof.
    iIntros (????) "Ha Hb Hc Hd". rel_rec_r. repeat rel_pure_r.
    rel_rec_r.
    repeat rel_pure_r. rel_alloc_r c2 as "Hc2".
    repeat rel_pure_r. rel_fork_r i as "Hi".
    { simpl. eauto. }
    repeat rel_pure_r.
    tp_rec i. simpl.
    rel_rec_l. repeat rel_pure_l.
    rewrite {5}refines_eq /refines_def.
    iIntros (j K) "#Hs Hj". iModIntro.
    pose (N:=nroot.@"par").
    wp_bind (spawn _).
    iApply (spawn_spec N with "[Ha Hj]").
    - wp_lam. rewrite refines_eq /refines_def.
      tp_bind j a.
      iMod ("Ha" with "Hs Hj") as "Ha".
      iExact "Ha".
    - iNext. iIntros (h) "Hdl". wp_pures.
      wp_bind b.
      rewrite {1}refines_eq /refines_def.
      tp_bind i b.
      iMod ("Hb" with "Hs Hi") as "Hb".
      iApply (wp_wand with "Hb").
      iIntros (bv). iDestruct 1 as (bv') "[Hi HB]". simpl.
      wp_pures. wp_bind (spawn.join _).
      iApply (join_spec with "Hdl").
      iNext. iIntros (av). iDestruct 1 as (av') "[Hj HA]".
      wp_pures. tp_pures j. tp_pures i.
      wp_rec. wp_pures.
      wp_apply (spawn_spec N with "[Hc Hi]").
      { wp_pures.
        rewrite refines_eq /refines_def.
        tp_bind i c.
        iMod ("Hc" with "Hs Hi") as "Hc". iExact "Hc". }
      clear h. iIntros (h) "Hdl". wp_pures.
      wp_bind d.
      rewrite refines_eq /refines_def.
      tp_bind j d.
      iMod ("Hd" with "Hs Hj") as "Hd".
      iApply (wp_wand with "Hd"). iIntros (dv).
      iDestruct 1 as (dv') "[Hj HD]".
      wp_pures. wp_apply (join_spec with "Hdl").
      iIntros (cv). iDestruct 1 as (cv') "[Hi HC]".
      iApply wp_fupd.
      wp_pures. iExists (cv', dv')%V. simpl.
      tp_pures i. tp_store i.
      tp_pures j.
      rewrite /spawn.join. tp_pures j.
      tp_load j. tp_pures j. eauto with iFrame.
  Qed.
End rules.
