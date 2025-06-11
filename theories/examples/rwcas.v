From reloc Require Export reloc.
From reloc.lib Require Import lock.
Set Default Proof Using "Type".

From reloc Require Import reloc lib.lock.
From iris.algebra Require Import numbers csum excl auth list gmap gset.
From iris.base_logic.lib Require Import token.
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
    Resolve (CmpXchg "l" !"l" "v") "p" #();;
    #().

(* Fine-grained implementatiaon of a read-write cell *)
Definition lf_rwcas : val := λ: <>,
  let: "x" := ref #0 in
  ((λ: "v", lf_write "x" "v"), (λ: <>, read "x")).

(* LP stepping requests. *)
(* Map the proph id of every failing write to a triple [(id, γₜ, v)]*)
Definition requestReg := gmap nat (agree (ref_id * gname * Z)).
Definition requestRegUR := authUR $ gmapUR nat (agreeR (prodO (prodO ref_idO gnameO) ZO)).

Check to_agree_op_inv_L.

Class rwcasG Σ := {
  rwcas_requestUR :: inG Σ requestRegUR;
}.

Section wf.

  Context `{!relocG Σ, !rwcasG Σ, !tokenG Σ}.

  Definition rwcasN : namespace := nroot .@ "rwcas".

  Definition extract_result (vs : list (val * val)) : option (bool * Z) :=
    match vs with
    | (PairV (LitV (LitInt n)) (LitV (LitBool b)), _) :: _ => Some (b, n)
    | _ => None (* (true, LitV LitUnit) *)
    end.

  Definition ids_at γₘ p id := own γₘ (◯ {[ p := to_agree id ]}).

  Check ids_at.

  (* Definition rwcas_inv γₘ lᵢ lₛ : iProp Σ :=
    ∃ (n : Z) pvs ps, 
      lᵢ ↦ #n ∗ (* implementation location *)
      lₛ ↦ₛ #n ∗ (* spec location*)

      proph_map_interp pvs ps ∗ (* Authoritative ownership over prophecy map *)
      [∗ set] p ∈ ps, (* For every thread/proph id *)
        ∀ m, ⌜extract_result (proph_list_resolves pvs p) = Some (false, m)⌝ → (* If the cmpxchg fails *)
          ∃ id, 
            ids_at γₘ p id ∗ (* The thread/proph id [p] is bound to refinement id [id]*)
              (refines_right id #()) ∨ (* The failing write has already been linearized and the spec of its right refinement has already been reduced to [()] *)
              (⌜n ≠ m⌝ ∗ ∃ (p : Z), refines_right id (atomic_write #lₛ #p)) ∨
              (* Or the value currently stored in the cell is not what the failing cmpxchg will eventually read from the cell.
                 Thus, there exists some future sucessful write that will cause it to fail. 
                 The invariant contains the un-reduced left refinement for this writer to reduce *) *)

  Definition registry_inv lₛ n (requests : list (ref_id * gname * Z)) : iProp Σ :=
    [∗ list] '(id, γₜ, m) ∈ requests, (* For every thread/proph id *)
        (refines_right id #() ∨ (* The failing write has already been linearized and the spec of its right refinement has already been reduced to [()] *)
        (⌜m ≠ n⌝ ∗ ∃ (p : Z), refines_right id (atomic_write #lₛ #p)) ∨
          (* Or the value currently stored in the cell is not what the failing cmpxchg will eventually read from the cell.
              Thus, there exists some future sucessful write that will cause it to fail. 
              The invariant contains the un-reduced left refinement for this writer to reduce *)
        token γₜ).
        (* The failing write has linearized and returned *)

  Definition rwcas_inv (γ : gname) lᵢ lₛ : iProp Σ :=
    ∃ (n : Z) (requests : list (ref_id * gname * Z)), 
      lᵢ ↦ #n ∗ (* implementation location *)
      lₛ ↦ₛ #n ∗ (* spec location*)
      own γ (● map_seq O (to_agree <$> requests)) ∗ (* Authoritative ownership over prophecy map *)
      registry_inv lₛ n requests.

  Lemma refines_right_write E l (m n p : Z) requests :
    nclose relocN ⊆ E →
      l ↦ₛ #m -∗ 
        registry_inv l n requests ={E}=∗ 
          registry_inv l p requests ∗ ∃ q : Z, l ↦ₛ #q.
  Proof.
    iIntros (HNE) "Hl Hreqs".
    iInduction requests as [|[[id γₜ] m'] reqs'] "IH" forall (m).
    - by iFrame.
    - rewrite /registry_inv. do 2 rewrite -> big_sepL_cons by done.
      iDestruct "Hreqs" as "[[Hlin | [(%Hne & %q' & Href) | Hresp]] Hreqs']";
      iMod ("IH" with "Hl Hreqs'") as "(Hreqs' & %q & Hl)".
      + iSplitR "Hl".
        * iSplitR "Hreqs'"; by iFrame.
        * by iFrame.
      + rewrite /atomic_write.
        tp_pures id.
        tp_store id.
        iSplitR "Hl".
          * iSplitR "Hreqs'"; by iFrame.
          * by iFrame.
      + iSplitR "Hl".
        * iSplitR "Hreqs'"; by iFrame.
        * by iFrame.
  Qed.
              
  Lemma read_refinement γₘ lᵢ lₛ :
    inv rwcasN (rwcas_inv γₘ lᵢ lₛ) -∗
    REL read #lᵢ << read #lₛ : lrel_int.
  Proof.
    iIntros "#Hinv".
    rewrite /read.
    rel_pure_l.
    rel_pure_r.
    rel_load_l_atomic.
    iInv rwcasN as (n requests) "(Hlᵢ & Hlₛ & H● & Hreq)" "Hclose".
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

  Lemma write_refinement γₘ lᵢ lₛ (q : Z) : 
    inv rwcasN (rwcas_inv γₘ lᵢ lₛ) -∗
    REL wf_write #lᵢ #q << atomic_write #lₛ #q : lrel_unit.
  Proof.
    iIntros "#Hinv".
    rewrite /wf_write /atomic_write.
    rel_pures_l.
    rel_newproph_l vs p as "Hₚ".
    rel_pures_l.
    rel_load_l_atomic.
    iInv rwcasN as (n reqs) "(Hlᵢ & Hlₛ & H● & Hreqs)" "Hclose".
    iExists #n.
    iSplitL "Hlᵢ"; first done.
    destruct (extract_result vs) as [[[|] m] | ] eqn:Hres.
    - (* We are destined to succeed *)
      iIntros "!> !> Hlᵢ".
      (* Close invariant with same request registry *)
      iMod ("Hclose" with "[Hlᵢ Hlₛ H● Hreqs]") as "_".
      { iFrame. }
      clear reqs.
      rel_apply_l refines_resolveatomic_l.
      { done. }
      iInv rwcasN as (n' reqs) "(Hlᵢ & Hlₛ & H● & Hreqs)" "Hclose".
      iExists _. iFrame.
      iModIntro.
      destruct (decide (n' = n)) as [-> | Hne].
      + (* Consistent with the prophecy, we suceed *)
        wp_cmpxchg_suc.
        iIntros "!> %vs' -> _".
        rel_pures_l.
        iMod (refines_right_write _ _ _ _ q with "Hlₛ Hreqs") as "(Hreqs & %q' & Hlₛ)".
        { solve_ndisj. }
        rel_store_r.
        iMod ("Hclose" with "[Hlᵢ Hlₛ H● Hreqs]") as "_".
        { iFrame. }
        rel_values. 
      + (* Contrary to the prophecy, the CmpXchg fails *)
        wp_cmpxchg_fail.
        iIntros "!> %vs' -> _".
        simplify_eq.
    - (* We are destined to fail *)
      destruct (decide (n = m)) as [-> | Hne].
      + (* The value propecized to be read at the cmpxchg is the same
           as the load. This is impossible; the CmpXchg will suceed *)
        admit.
      + iMod token_alloc as "[%γₜ Hγₜ]".
        iIntros "!> !> Hlᵢ".
        iApply refines_split.
        iIntros (id) ("Hrht").
        iMod (own_update with "H●") as "[H● H◯]".
        { eapply auth_update_alloc.
          apply alloc_singleton_local_update 
            with 
              (i := length reqs)
              (x := to_agree (id, γₜ, m)).
          { rewrite lookup_map_seq_None length_fmap. by right. }
          constructor. }
        replace (length reqs) with (O + length (to_agree <$> reqs)) at 1 
          by (now rewrite length_fmap).
        rewrite -map_seq_snoc.
        iMod ("Hclose" with "[Hlᵢ Hlₛ H● Hreqs Hrht]") as "_".
        { iExists _, (reqs ++ [(id, γₜ, m)]). 
          rewrite fmap_snoc. iFrame.
          rewrite big_sepL_singleton.
          iRight. iLeft. iSplitR; by iFrame. }
        rel_apply_l refines_resolveatomic_l.
        { done. }
        iExists _. iFrame.
        iInv rwcasN as (n' reqs') "(Hlᵢ & Hlₛ & H● & Hreqs')" "Hclose".
        iModIntro.
        destruct (decide (n' = n)) as [-> | Hneq].
        * wp_cmpxchg_suc.
          iIntros "!> %vs' -> _". simplify_eq.
        * wp_cmpxchg_fail.
          iIntros "!> %vs' -> _".
          inv Hres.
          iCombine "H● H◯" gives %[Hincl Hv]%auth_both_valid_discrete.
          apply dom_included in Hincl as Hdom.
          rewrite dom_singleton_L singleton_subseteq_l in Hdom.
          rewrite lookup_included in Hincl.
          specialize Hincl with (length reqs).
          rewrite option_included in Hincl.
          destruct Hincl as [Hnone | (a & b & H & H' & Heq)].
          { by rewrite lookup_insert in Hnone. }
          rewrite lookup_insert in H. simplify_eq.
          destruct Heq as [Heq | Hle].
          -- rewrite lookup_map_seq_0 in H'.
             assert (∃ b' : (agree (ref_id * gname * Z)), b = b') as [b' ->].
             { by exists b. }

             pose proof (lookup_fmap_Some to_agree _ _ _ H').
             rewrite list_lookup_fmap_Some in H'.
             rewrite lookup_fmap_Some in H'.
            Check lookup_fmap_Some.
             rewrite /registry_inv.
             iPoseProof (big_sepL_lookup _ _ _ _ H' with "[Hreqs']") as "Hl".
             { }
             apply big_sepL_lookup in H'.
          rewrite -Heq in H'. rewrite -{1}Heq in H'. inv Heq.
          rewrite
          unfold "≼" in H.
          rewrite dom_singleton_L in H.
          assert ({[length reqs]} ⊆ dom (map_seq 0 reqs'))
          admit.
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
