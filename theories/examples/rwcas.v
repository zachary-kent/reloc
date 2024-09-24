From reloc Require Export reloc.
From reloc.lib Require Import lock.
Set Default Proof Using "Type".

(** A course-grained write function that acquires a lock, performs the write, and then releases the lock *)
Definition CG_write : val := λ: "x" "v", "x" <- "v".

(** Can read the cell simply by derefencing it *)
Definition read : val := λ: "x",  !"x".

(* Course-grained implementatiaon of a read-write cell *)
Definition CG_rwcas : val := λ: <>,
  let: "x" := ref #0 in
  ((λ: "v", CG_write "x" "v"), (λ: <>, read "x")).

(** Fine-grained, strongly linearizable implementation of a read-write cell. 
    Read from the cell and attempt to CAS; loop until success *)
Definition FG_write : val := rec: "write" "x" "v" :=
  let: "c" := !"x" in
  if: CAS "x" "c" "v"
  then #()
  else "write" "x" "v".

Definition wkwrite : val := λ: "l" "v",
  "l" <- "v".

(* Fine-grained implementatiaon of a read-write cell *)
Definition FG_rwcas : val := λ: <>,
  let: "x" := ref #0 in
  ((λ: "v", FG_write "x" "v"), (λ: <>, read "x")).

Section CG_rwcas.
  Context `{relocG Σ}.

  Lemma read_r E K x (n : Z) t A
    (Hspec : nclose specN ⊆ E) :
    x ↦ₛ #n -∗
    (x ↦ₛ #n -∗ REL t << fill K (of_val #n) @ E : A) -∗ (* TODO: of_val *)
    REL t << fill K (read #x) @ E : A.
  Proof.
    iIntros "Hx Hlog".
    rel_rec_r. repeat rel_pure_r. rel_load_r.
    by iApply "Hlog".
  Qed.

  (* A similar atomic specification for the counter_read fn *)
  Lemma read_atomic_l R P E K x t A :
    P -∗
    □ (|={⊤,E}=> ∃ n : Z, x ↦ #n ∗ R n ∗
       (x ↦ #n ∗ R n ={E,⊤}=∗ True) ∧
        (x ↦ #n ∗ R n -∗ P -∗
            REL fill K (of_val #n) << t @ E : A))
    -∗ REL fill K (read #x) << t : A.
  Proof.
    iIntros "HP #H".
    rel_rec_l. repeat rel_pure_l. rel_load_l_atomic.
    iMod "H" as (n) "[Hx [HR Hfin]]". iModIntro.
    iExists _; iFrame "Hx". iNext.
    iIntros "Hx".
    iDestruct "Hfin" as "[_ Hfin]".
    iApply ("Hfin" with "[Hx HR] HP"). by iFrame.
  Qed.

  Definition rwcasN : namespace := nroot .@ "rwcas".

  Definition rwcas_inv x x' : iProp Σ :=
    (∃ n : Z, x ↦ #n ∗ x' ↦ₛ #n)%I.

  Definition counterN : namespace := nroot .@ "counter".

  Definition counter_inv lk cnt cnt' : iProp Σ :=
    (∃ n : Z, is_locked_r lk false ∗ cnt ↦ #n ∗ cnt' ↦ₛ #n)%I.

 (* A logically atomic specification for
     a fine-grained write with a baked in frame. *)
  Lemma FG_write_atomic_l R P E K x v t A  :
    P -∗
    □ (|={⊤,E}=> ∃ n : Z, x ↦ #n ∗ R n ∗
       ((x ↦ #n ∗ R n ={E,⊤}=∗ True) ∧
        (x ↦ #v ∗ R n -∗ P -∗
            REL fill K (of_val #()) << t @ E : A)))
    -∗ REL fill K (FG_write #x #v) << t : A.
  Proof.
    iIntros "HP #H".
    iLöb as "IH".
    rel_rec_l. repeat rel_pure_l.
    iPoseProof "H" as "H2".
    rel_load_l_atomic.
    iMod "H" as (n) "[Hx [HR Hrev]]".  iModIntro.
    iExists #n. iFrame. iNext. iIntros "Hx".
    iDestruct "Hrev" as "[Hrev _]".
    iMod ("Hrev" with "[HR Hx]") as "_"; first iFrame.
    repeat rel_pure_l. rel_cmpxchg_l_atomic.
    iMod "H2" as (n') "[Hx [HR HQ]]". iModIntro. simpl.
    destruct (decide (n = n')); subst.
    - iExists #n'. iFrame. simpl.
      iSplitR; eauto. { iDestruct 1 as %Hfoo. exfalso. done. }
      iIntros "_ !> Hx". simpl.
      iDestruct "HQ" as "[_ HQ]".
      replace (n' + 1)%Z with (1 + n')%Z; last by lia. (* TODO :( *)
      iSpecialize ("HQ" with "[$Hx $HR]").
      rel_pures_l. by iApply "HQ".
    - iExists #n'. iFrame. simpl.
      iSplitL; eauto; last first.
      { iDestruct 1 as %Hfoo. exfalso. simplify_eq. }
      iIntros "_ !> Hx". simpl.
      rel_pures_l.
      iDestruct "HQ" as "[HQ _]".
      iMod ("HQ" with "[$Hx $HR]").
      by iApply "IH".
  Qed.

  Lemma FG_CG_write_refinement x x' v1 v2 :
    inv rwcasN (rwcas_inv x x') -∗ lrel_int v1 v2 -∗
    REL FG_write #x v1 << CG_write #x' v2 : lrel_unit.
  Proof.
    iIntros "#Hinv".
    iIntros "(%v & -> & ->)".
    rel_apply_l
      (FG_write_atomic_l
              (fun n => x' ↦ₛ #n)%I
              True%I); first done.
    iModIntro. iInv rwcasN as ">Hcnt" "Hcl". iModIntro.
    iDestruct "Hcnt" as (n) "[Hcnt Hcnt']".
    iExists _; iFrame.
    iSplit.
    - iIntros "(Hcnt & Hcnt')".
      iApply ("Hcl" with "[-]").
      iNext. iExists _. iFrame.
    - iIntros "(Hcnt & Hcnt') _".
      unfold CG_write. rel_pures_r.
      rel_store_r.
      iMod ("Hcl" with "[-]").
      { iNext. iExists v; iFrame. }
      rel_values.
  Qed.

  Lemma read_refinement x x' :
    inv rwcasN (rwcas_inv x x') -∗
    REL read #x << read #x' : lrel_int.
  Proof.
    iIntros "#Hinv".
    rel_apply_l
      (read_atomic_l
         (fun n => x' ↦ₛ #n)%I
         True%I); first done.
    iModIntro. iInv rwcasN as (n) "[>Hcnt >Hcnt']" "Hclose".
    iModIntro.
    iExists n. iFrame "Hcnt Hcnt'".
    iSplit.
    - iIntros "(Hcnt & Hcnt')". iApply "Hclose".
      iNext. iExists n. by iFrame.
    - iIntros "(Hcnt & Hcnt') _ /=".
      rel_apply_r (read_r with "Hcnt'").
      iIntros "Hcnt'".
      iMod ("Hclose" with "[Hcnt Hcnt']"); simpl.
      { iNext. iExists _. by iFrame. }
      rel_values.
  Qed.

  Lemma FG_CG_rwcas_refinement :
    ⊢ REL FG_rwcas << CG_rwcas : () → (lrel_int → ()) * (() → lrel_int).
  Proof.
    iApply refines_arrow_val.
    iModIntro. iIntros (? ?) "_"; simplify_eq/=.
    rel_rec_l. rel_rec_r.
    rel_alloc_r cnt' as "Hcnt'".
    rel_alloc_l cnt as "Hcnt". simpl.

    (* establishing the invariant *)
    iAssert (rwcas_inv cnt cnt')
      with "[Hcnt Hcnt']" as "Hinv".
    { iExists 0. by iFrame. }
    iMod (inv_alloc rwcasN with "[Hinv]") as "#Hinv"; trivial.

    (* TODO: here we have to do /exactly/ 4 steps.
       The next step will reduce `(Val v1, Val v2)` to `Val (v1, v2)`,
       and the compatibility rule wouldn't be applicable *)
    do 4 rel_pure_r. do 4 rel_pure_l.
    iApply refines_pair.
    - iApply refines_arrow_val.
      iModIntro. iIntros (? ?) "Hrel". rel_seq_l; rel_seq_r.
      iApply (FG_CG_write_refinement with "Hinv"). iFrame.
    - iApply refines_arrow_val.
      iModIntro. iIntros (? ?) "_". rel_seq_l; rel_seq_r.
      iApply (read_refinement with "Hinv").
  Qed.

End CG_rwcas.

Theorem rwcas_ctx_refinement :
  ∅ ⊨ FG_rwcas ≤ctx≤ CG_rwcas :
         () → ((TNat → ()) * (() → TNat)).
Proof.
  eapply (refines_sound relocΣ).
  iIntros (? Δ). simpl. iApply FG_CG_rwcas_refinement.
Qed.
