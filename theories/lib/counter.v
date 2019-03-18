From reloc Require Export reloc.
From reloc.lib Require Import lock.
Set Default Proof Using "Type".

Definition CG_increment : val := λ: "x" "l",
  acquire "l";;
  let: "n" := !"x" in
  "x" <- #1 + "n";;
  release "l";;
  "n".

Definition counter_read : val := λ: "x",  !"x".

Definition CG_counter : val := λ: <>,
  let: "l" := newlock #() in
  let: "x" := ref #0 in
  ((λ: <>, CG_increment "x" "l"), (λ: <>, counter_read "x")).

Definition FG_increment : val := rec: "inc" "v" :=
  let: "c" := !"v" in
  if: CAS "v" "c" (#1 + "c")
  then "c"
  else "inc" "v".

Definition wkincr : val := λ: "l",
  "l" <- !"l" + #1.

Definition FG_counter : val := λ: <>,
  let: "x" := ref #0 in
  ((λ: <>, FG_increment "x"), (λ: <>, counter_read "x")).

Section CG_Counter.
  Context `{relocG Σ}.

  Lemma CG_increment_r K E t A (x l : loc) (n : nat) :
    nclose specN ⊆ E →
    (x ↦ₛ # n -∗ l ↦ₛ #false -∗
    (x ↦ₛ # (n + 1) -∗ l ↦ₛ #false -∗
      (REL t << fill K (of_val #n) @ E : A)) -∗
    REL t << fill K (CG_increment #x #l) @ E : A)%I.
  Proof.
    iIntros (?) "Hx Hl Hlog".
    rel_rec_r.
    repeat rel_pure_r.
    rel_apply_r (refines_acquire_r with "Hl").
    iIntros "Hl".
    repeat rel_pure_r.
    rel_load_r. repeat rel_pure_r.
    rel_store_r. repeat rel_pure_r.
    rel_apply_r (refines_release_r with "Hl").
    iIntros "Hl". repeat rel_pure_r.
    replace (n + 1)%Z with (1 + n)%Z; last lia.
    by iApply ("Hlog" with "Hx Hl").
  Qed.

  Lemma counter_read_r E K x (n : nat) t A
    (Hspec : nclose specN ⊆ E) :
    x ↦ₛ #n -∗
    (x ↦ₛ #n -∗ REL t << fill K (of_val #n) @ E : A) -∗ (* TODO: of_val *)
    REL t << fill K (counter_read #x) @ E : A.
  Proof.
    iIntros "Hx Hlog".
    rel_rec_r. repeat rel_pure_r. rel_load_r.
    by iApply "Hlog".
  Qed.

  Lemma FG_increment_r K E t A (x : loc) (n : nat) :
    nclose specN ⊆ E →
    (x ↦ₛ # n -∗
    (x ↦ₛ #(n + 1) -∗
      REL t << fill K (of_val #n) @ E : A) -∗
    REL t << fill K (FG_increment #x) @ E : A)%I.
  Proof.
    iIntros (?) "Hx Hlog".
    rel_rec_r. repeat rel_pure_r.
    rel_load_r. repeat rel_pure_r.
    rel_cas_suc_r.
    rel_if_r.
    replace (n + 1)%Z with (1 + n)%Z; last lia.
    by iApply "Hlog".
  Qed.

  (* A logically atomic specification for
     a fine-grained increment with a baked in frame. *)
  Lemma FG_increment_atomic_l R P E K x t A  :
    P -∗
    □ (|={⊤,E}=> ∃ n : nat, x ↦ #n ∗ R n ∗
       ((x ↦ #n ∗ R n ={E,⊤}=∗ True) ∧
        (x ↦ #(n+1) ∗ R n -∗ P -∗
            REL fill K (of_val #n) << t @ E : A)))
    -∗ REL fill K (FG_increment #x) << t : A.
  Proof.
    iIntros "HP #H".
    iLöb as "IH".
    rel_rec_l. repeat rel_pure_l.
    iPoseProof "H" as "H2". (* lolwhat *)
    rel_load_l_atomic.
    iMod "H" as (n) "[Hx [HR Hrev]]".  iModIntro.
    iExists #n. iFrame. iNext. iIntros "Hx".
    iDestruct "Hrev" as "[Hrev _]".
    iMod ("Hrev" with "[HR Hx]") as "_"; first iFrame.
    repeat rel_pure_l. rel_cas_l_atomic.
    iMod "H2" as (n') "[Hx [HR HQ]]". iModIntro. simpl.
    destruct (decide (n = n')); subst.
    - iExists #n'. iFrame.
      iSplitR; eauto. { iDestruct 1 as %Hfoo. exfalso. done. }
      iIntros "_ !> Hx". simpl.
      iDestruct "HQ" as "[_ HQ]".
      replace (n' + 1)%Z with (1 + n')%Z; last by lia. (* TODO :( *)
      iSpecialize ("HQ" with "[$Hx $HR]").
      rel_if_true_l. by iApply "HQ".
    - iExists #n'. iFrame.
      iSplitL; eauto; last first.
      { iDestruct 1 as %Hfoo. exfalso. simplify_eq. }
      iIntros "_ !> Hx". simpl.
      rel_if_false_l.
      iDestruct "HQ" as "[HQ _]".
      iMod ("HQ" with "[$Hx $HR]").
      by iApply "IH".
  Qed.

  (* A similar atomic specification for the counter_read fn *)
  Lemma counter_read_atomic_l R P E K x t A :
    P -∗
    □ (|={⊤,E}=> ∃ n : nat, x ↦ #n ∗ R n ∗
       (x ↦ #n ∗ R n ={E,⊤}=∗ True) ∧
        (x ↦ #n ∗ R n -∗ P -∗
            REL fill K (of_val #n) << t @ E : A))
    -∗ REL fill K (counter_read #x) << t : A.
  Proof.
    iIntros "HP #H".
    rel_rec_l. repeat rel_pure_l. rel_load_l_atomic.
    iMod "H" as (n) "[Hx [HR Hfin]]". iModIntro.
    iExists _; iFrame "Hx". iNext.
    iIntros "Hx".
    iDestruct "Hfin" as "[_ Hfin]".
    iApply ("Hfin" with "[Hx HR] HP"). by iFrame.
  Qed.


  Definition counterN : namespace := nroot .@ "counter".

  Definition counter_inv l cnt cnt' : iProp Σ :=
    (∃ n : nat, l ↦ₛ #false ∗ cnt ↦ #n ∗ cnt' ↦ₛ #n)%I.

  Lemma FG_CG_increment_refinement l cnt cnt' :
    inv counterN (counter_inv l cnt cnt') -∗
    REL FG_increment #cnt << CG_increment #cnt' #l : lrel_int.
  Proof.
    iIntros "#Hinv".
    rel_apply_l
      (FG_increment_atomic_l
              (fun n => (l ↦ₛ #false) ∗ cnt' ↦ₛ #n)%I
              True%I); first done.
    iAlways. iInv counterN as ">Hcnt" "Hcl". iModIntro.
    iDestruct "Hcnt" as (n) "(Hl & Hcnt & Hcnt')".
    iExists _; iFrame.
    iSplit.
    - iIntros "(Hcnt & Hl & Hcnt')".
      iApply ("Hcl" with "[-]").
      iNext. iExists _. iFrame.
    - iIntros "(Hcnt & Hl & Hcnt') _".
      rel_apply_r (CG_increment_r with "Hcnt' Hl").
      iIntros "Hcnt' Hl".
      iMod ("Hcl" with "[-]").
      { iNext. iExists (n+1); iFrame.
        rewrite !Nat2Z.inj_add. by iFrame. }
      rel_values.
  Qed.

  Lemma counter_read_refinement l cnt cnt' :
    inv counterN (counter_inv l cnt cnt') -∗
    REL counter_read #cnt << counter_read #cnt' : lrel_int.
  Proof.
    iIntros "#Hinv".
    rel_apply_l
      (counter_read_atomic_l
         (fun n => (l ↦ₛ #false) ∗ cnt' ↦ₛ #n)%I
         True%I); first done.
    iAlways. iInv counterN as (n) "[>Hl [>Hcnt >Hcnt']]" "Hclose".
    iModIntro.
    iExists n. iFrame "Hcnt Hcnt' Hl".
    iSplit.
    - iIntros "(Hcnt & Hl & Hcnt')". iApply "Hclose".
      iNext. iExists n. by iFrame.
    - iIntros "(Hcnt & Hl & Hcnt') _ /=".
      rel_apply_r (counter_read_r with "Hcnt'").
      iIntros "Hcnt'".
      iMod ("Hclose" with "[Hl Hcnt Hcnt']"); simpl.
      { iNext. iExists _. by iFrame. }
      rel_values.
  Qed.

  Lemma FG_CG_counter_refinement :
    REL FG_counter << CG_counter : () → (() → lrel_int) * (() → lrel_int).
  Proof.
    unfold FG_counter, CG_counter.
    iApply refines_arrow_val.
    iAlways. iIntros (? ?) "_"; simplify_eq/=.
    rel_rec_l. rel_rec_r.
    rel_apply_r refines_newlock_r; auto.
    iIntros (l) "Hl".
    repeat rel_pure_r.
    rel_alloc_r cnt' as "Hcnt'".
    rel_alloc_l cnt as "Hcnt". simpl.

    (* establishing the invariant *)
    iAssert (counter_inv l cnt cnt')
      with "[Hl Hcnt Hcnt']" as "Hinv".
    { iExists 0. by iFrame. }
    iMod (inv_alloc counterN with "[Hinv]") as "#Hinv"; trivial.

    (* TODO: here we have to do /exactly/ 4 steps.
       The next step will reduce `(Val v1, Val v2)` to `Val (v1, v2)`,
       and the compatibility rule wouldn't be applicable *)
    do 4 rel_pure_r. do 4 rel_pure_l.
    iApply refines_pair .
    - iApply refines_arrow_val.
      iAlways. iIntros (? ?) "_". rel_seq_l; rel_seq_r.
      iApply (FG_CG_increment_refinement with "Hinv").
    - iApply refines_arrow_val.
      iAlways. iIntros (? ?) "_". rel_seq_l; rel_seq_r.
      iApply (counter_read_refinement with "Hinv").
  Qed.
End CG_Counter.

Theorem counter_ctx_refinement :
  ∅ ⊨ FG_counter ≤ctx≤ CG_counter :
         TUnit → ((TUnit → TNat) * (TUnit → TNat)).
Proof.
  eapply (refines_sound relocΣ).
  iIntros (? Δ). iApply FG_CG_counter_refinement.
Qed.
