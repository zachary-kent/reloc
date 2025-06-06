From reloc Require Export reloc.
From reloc.lib Require Import lock.
Set Default Proof Using "Type".

From reloc Require Import reloc lib.lock.
From iris.algebra Require Import numbers csum excl auth list gmap gset.
From iris.bi.lib Require Export fixpoint.


Definition atomic_write : val := λ: "x" "v", "x" <- "v".

(** Can read the cell simply by derefencing it *)
Definition read : val := λ: "x",  !"x".

(* Course-grained implementatiaon of a read-write cell *)
Definition atomic_rwcas : val := λ: <>,
  let: "x" := ref #0 in
  ((λ: "v", atomic_write "x" "v"), (λ: <>, read "x")).

(** Fine-grained, strongly linearizable implementation of a read-write cell. 
    Read from the cell and attempt to CAS; loop until success *)
Definition lf_write : val :=
  rec: "write" "x" "v" :=
    let: "c" := !"x" in
    if: CAS "x" "c" "v"
      then #()
      else "write" "x" "v".

Definition wf_write : val :=
  λ: "l" "v",
    let: "p" := NewProph in
    Resolve (CmpXchg "l" !"l" "v") "p" #().

(* Fine-grained implementatiaon of a read-write cell *)
Definition lf_rwcas : val := λ: <>,
  let: "x" := ref #0 in
  ((λ: "v", lf_write "x" "v"), (λ: <>, read "x")).

(* LP stepping requests. *)
Definition requestReg := gmap proph_id ref_id.
Definition requestRegUR := authUR $ gmapUR proph_id (agreeR ref_idO).

Class rwcasG Σ := {
  rwcas_requestUR :: inG Σ requestRegUR;
}.

Section wf.

  Context `{!relocG Σ, !rwcasG Σ}.

  Definition rwcasN : namespace := nroot .@ "rwcas".

  Definition extract_result (vs : list (val * val)) : option (bool * Z) :=
    match vs with
    | (_, PairV (LitV (LitBool b)) (LitV (LitInt n))) :: _ => Some (b, n)
    | _ => None (* (true, LitV LitUnit) *)
    end.

  Definition ids_at γₘ p id := own γₘ (◯ {[ p := to_agree id ]}).

  Definition rwcas_inv γₘ lᵢ lₛ : iProp Σ :=
    ∃ (n : Z) pvs ps, 
      lᵢ ↦ #n ∗ (* implementation location *)
      lₛ ↦ₛ #n ∗ (* spec location*)
      proph_map_interp pvs ps ∗ (* Authoritative ownership over prophecy map *)
      [∗ set] p ∈ ps, (* For every thread/proph id *)
        ∀ m, ⌜extract_result (proph_list_resolves pvs p) = Some (false, m)⌝ → (* If the cmpxchg fails *)
          ∃ id, 
            ids_at γₘ p id ∗ (* The thread/proph id [p] is bound to refinement id [id]*)
              (refines_right id #()) ∨ (* The failing write has already been linearized; the spec of its right refinement has already been reduced to [()] *)
              (⌜n ≠ m⌝ ∗ ∃ (p : Z), refines_right id (atomic_write #lₛ #p)).
              (* Or the value currently stored in the cell is not what the failing cmpxchg will eventually read from the cell.
                 Thus, there exists some future sucessful write that will cause it to fail. 
                 The invariant contains the un-reduced left refinement for this writer to reduce *)


  Lemma read_refinement γₘ lᵢ lₛ :
    inv rwcasN (rwcas_inv γₘ lᵢ lₛ) -∗
    REL read #lᵢ << read #lₛ : lrel_int.
  Proof.
    iIntros "#Hinv".
    rewrite /read.
    rel_pure_l.
    rel_pure_r.
    rel_load_l_atomic.
    iInv rwcasN as (n pvs ps) "(Hlᵢ & Hlₛ & H● & Hproph)" "Hclose".
    iExists #n.
    iSplitL "Hlᵢ"; first done.
    iIntros "!> !> Hli".
    rel_load_r.
    rel_values.
    iApply fupd_mono.
    - iIntros "_".
      by iExists _.
    - iApply "Hclose".
      iFrame.
  Qed.

End wf.

Section atomic_rwcas.
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

  (* A similar atomic specification for the read fn *)
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

 (* A logically atomic specification for
     a fine-grained write with a baked in frame. *)
  Lemma lf_write_atomic_l R P E K x v t A  :
    P -∗
    □ (|={⊤,E}=> ∃ n : Z, x ↦ #n ∗ R n ∗
       ((x ↦ #n ∗ R n ={E,⊤}=∗ True) ∧
        (x ↦ #v ∗ R n -∗ P -∗
            REL fill K (of_val #()) << t @ E : A)))
    -∗ REL fill K (lf_write #x #v) << t : A.
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
      replace (n' + 1)%Z with (1 + n')%Z by lia. (* TODO :( *)
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

  Lemma FG_atomic_write_refinement x x' v1 v2 :
    inv rwcasN (rwcas_inv x x') -∗ lrel_int v1 v2 -∗
    REL lf_write #x v1 << atomic_write #x' v2 : lrel_unit.
  Proof.
    iIntros "#Hinv".
    iIntros "(%v & -> & ->)".
    rel_apply_l
      (lf_write_atomic_l
              (fun n => x' ↦ₛ #n)%I
              True%I); first done.
    iModIntro. iInv rwcasN as ">Hv" "Hcl". iModIntro.
    iDestruct "Hv" as (n) "[Hv Hv']".
    iExists _; iFrame.
    iSplit.
    - iIntros "(Hv & Hv')".
      iApply ("Hcl" with "[-]").
      iNext. iExists _. iFrame.
    - iIntros "(Hv & Hv') _".
      unfold atomic_write. rel_pures_r.
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
    iModIntro. iInv rwcasN as (n) "[>Hv >Hv']" "Hclose".
    iModIntro.
    iExists n. iFrame "Hv Hv'".
    iSplit.
    - iIntros "(Hv & Hv')". iApply "Hclose".
      iNext. iExists n. by iFrame.
    - iIntros "(Hv & Hv') _ /=".
      rel_apply_r (read_r with "Hv'").
      iIntros "Hv'".
      iMod ("Hclose" with "[Hv Hv']"); simpl.
      { iNext. iExists _. by iFrame. }
      rel_values.
  Qed.

  Lemma FG_atomic_rwcas_refinement :
    ⊢ REL lf_rwcas << atomic_rwcas : () → (lrel_int → ()) * (() → lrel_int).
  Proof.
    iApply refines_arrow_val.
    iModIntro. iIntros (? ?) "_"; simplify_eq/=.
    rel_rec_l. rel_rec_r.
    rel_alloc_r v' as "Hv'".
    rel_alloc_l v as "Hv". simpl.

    (* establishing the invariant *)
    iAssert (rwcas_inv v v')
      with "[Hv Hv']" as "Hinv".
    { iExists 0. by iFrame. }
    iMod (inv_alloc rwcasN with "[Hinv]") as "#Hinv"; trivial.

    (* TODO: here we have to do /exactly/ 4 steps.
       The next step will reduce `(Val v1, Val v2)` to `Val (v1, v2)`,
       and the compatibility rule wouldn't be applicable *)
    do 4 rel_pure_r. do 4 rel_pure_l.
    iApply refines_pair.
    - iApply refines_arrow_val.
      iModIntro. iIntros (? ?) "Hrel". rel_seq_l; rel_seq_r.
      iApply (FG_atomic_write_refinement with "Hinv"). iFrame.
    - iApply refines_arrow_val.
      iModIntro. iIntros (? ?) "_". rel_seq_l; rel_seq_r.
      iApply (read_refinement with "Hinv").
  Qed.

End atomic_rwcas.

Theorem rwcas_ctx_refinement :
  ∅ ⊨ lf_rwcas ≤ctx≤ atomic_rwcas :
         () → ((TNat → ()) * (() → TNat)).
Proof.
  eapply (refines_sound relocΣ).
  iIntros (? Δ). simpl. iApply FG_atomic_rwcas_refinement.
Qed.
