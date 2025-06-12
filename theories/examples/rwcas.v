From reloc Require Import reloc.
From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import token.

Definition atomic_write : val := λ: "x" "v", "x" <- "v".

(** Can read the cell simply by derefencing it *)
Definition read : val := λ: "x",  !"x".

(* Course-grained implementatiaon of a read-write cell *)
Definition atomic_rwcas : val := λ: <>,
  let: "x" := ref #0 in
  ((λ: "v", atomic_write "x" "v"), (λ: <>, read "x")).

Definition wf_write : val :=
  λ: "l" "v",
    let: "p" := NewProph in
    Resolve (CmpXchg "l" !"l" "v") "p" #();;
    #().

(* Fine-grained implementatiaon of a read-write cell *)
Definition wf_rwcas : val := λ: <>,
  let: "x" := ref #0 in
  ((λ: "v", wf_write "x" "v"), (λ: <>, read "x")).

(* LP stepping requests. *)
(* Map the process id of every failing write to a triple [(id, γₜ, v)]*)
Definition requestReg := gmap nat (agree (ref_id * gname * Z)).
Definition requestRegUR := authUR $ gmapUR nat (agreeR (prodO (prodO ref_idO gnameO) ZO)).

Class rwcasG Σ := {
  rwcas_requestUR :: inG Σ requestRegUR;
}.

Section wf.

  Context `{!relocG Σ, !rwcasG Σ, !tokenG Σ}.

  Definition rwcasN : namespace := nroot .@ "rwcas".

  Definition extract_result (vs : list (val * val)) : option (bool * Z) :=
    match vs with
    | (PairV (LitV (LitInt n)) (LitV (LitBool b)), _) :: _ => Some (b, n)
    | _ => None
    end.

  Definition registry_inv lₛ n (requests : list (ref_id * gname * Z)) : iProp Σ :=
    [∗ list] '(id, γₜ, m) ∈ requests, (* For every thread/proph id *)
        (refines_right id #() ∨ (* The failing write has already been linearized and the spec of its right refinement has already been reduced to [()] *)
        (⌜m ≠ n⌝ ∗ ∃ (p : Z), refines_right id (atomic_write #lₛ #p)) ∨
          (* Or the value currently stored in the cell is not what the failing cmpxchg will eventually read from the cell.
              Thus, there exists some future sucessful write that will cause it to fail. 
              The invariant contains the un-reduced left refinement for this writer to reduce *)
        token γₜ).
        (* The failing write has linearized and returned *)

  (* Authoritative ownership over request registry *)
  Definition registry γ (requests : list (ref_id * gname * Z)) :=
    own γ (● map_seq O (to_agree <$> requests)).

  (* Fragmental ownership over a single request *)
  Definition registered γ i (id : ref_id) (γₜ : gname) (m : Z) :=
   own γ (◯ ({[i := to_agree (id, γₜ, m)]})).

  Definition rwcas_inv (γ : gname) lᵢ lₛ : iProp Σ :=
    ∃ (n : Z) (requests : list (ref_id * gname * Z)), 
      lᵢ ↦ #n ∗ (* implementation location *)
      lₛ ↦ₛ #n ∗ (* spec location*)
      registry γ requests ∗ (* Authoritative ownership over request registry *)
      registry_inv lₛ n requests.

  (* Frame-preserving updates permit allocation of a new request *)
  Lemma registry_update id γₜ m γ requests : 
    registry γ requests ==∗ 
      registry γ (requests ++ [(id, γₜ, m)]) ∗ registered γ (length requests) id γₜ m.
  Proof.
    iIntros "H●".
    rewrite /registry /registered.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length requests)
          (x := to_agree (id, γₜ, m)).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length requests) with (O + length (to_agree <$> requests)) at 1 
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  (* The authoritative view of the request registry must agree with its fragment *)
  Lemma registry_agree (requests : list (ref_id * gname * Z)) i id γₜ m : 
    ✓ (● map_seq O (to_agree <$> requests) ⋅ ◯ ({[i := to_agree (id, γₜ, m)]})) →
        requests !! i = Some (id, γₜ, m).
  Proof.
    intros [Hincl _]%auth_both_valid_discrete.
    apply dom_included in Hincl as Hdom.
    rewrite dom_singleton_L singleton_subseteq_l in Hdom.
    rewrite lookup_included in Hincl.
    specialize Hincl with i.
    rewrite option_included in Hincl.
    destruct Hincl as [Hnone | (a & b & H & H' & Heq)].
    { by rewrite lookup_insert in Hnone. }
    rewrite lookup_insert in H. simplify_eq.
    rewrite lookup_map_seq_0 list_lookup_fmap_Some in H'.
    destruct H' as ([[id' γₜ'] m'] & Hlookup & ->).
    destruct Heq as [Heq | Hle].
    - apply (inj to_agree) in Heq.
      by simplify_eq.
    - rewrite to_agree_included in Hle.
      by simplify_eq.
  Qed.

  (* It is possible to linearize pending writers while maintaing the registry invariant *)
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
  
  (* Implementation read refines the specification read. 
    This is trivial, as both reads are implemented identically *)
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

  (* Implementation write refines the specification write. *)
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
        (* We linearize any pending failing writers registered in the registry *)
        iMod (refines_right_write _ _ _ _ q with "Hlₛ Hreqs") as "(Hreqs & %q' & Hlₛ)".
        { solve_ndisj. }
        rel_store_r.
        iMod ("Hclose" with "[Hlᵢ Hlₛ H● Hreqs]") as "_".
        { iFrame. }
        rel_values. 
      + (* Contrary to the prophecy, the CmpXchg fails *)
        wp_cmpxchg_fail.
        iIntros "!> %vs' -> _ //".
    - (* We are destined to fail *)
      destruct (decide (n = m)) as [-> | Hne].
      + (* The value propecized to be read at the cmpxchg is the same
           as the load. This is impossible; the CmpXchg will suceed *)
        iIntros "!> !> Hlᵢ".
        iMod ("Hclose" with "[$]") as "_".
        rel_apply_l refines_resolveatomic_l.
        { done. }
        iInv rwcasN as (n' reqs') "(Hlᵢ & Hlₛ & H● & Hreqs')" "Hclose".
        iExists _. iFrame.
        iModIntro.
        destruct (decide (n' = m)) as [-> | Hneq].
        * wp_cmpxchg_suc.
          iIntros "!> %vs' -> _ //".
        * wp_cmpxchg_fail.
          iIntros "!> %vs' -> Hp".
          inv Hres.
      + (* Allocate a token. We will hold onto this until we return *)
        iMod token_alloc as "[%γₜ Hγₜ]".
        iIntros "!> !> Hlᵢ".
        (* Split the refinement, as the linearization point is external *)
        iApply refines_split.
        iIntros (id) "Hrht".
        (* Allocate a new linearization request in the registry for this failing writer *)
        iMod (registry_update id γₜ m with "H●") as "[H● H◯]".
        (* Close the invariant with the updated registry *)
        iMod ("Hclose" with "[Hlᵢ Hlₛ H● Hreqs Hrht]") as "_".
        { iExists _, (reqs ++ [(id, γₜ, m)]). 
          iFrame.
          rewrite big_sepL_singleton.
          iRight. iLeft. iSplitR; by iFrame. }
        rel_apply_l refines_resolveatomic_l.
        { done. }
        iExists _. iFrame.
        iInv rwcasN as (n' reqs') "(Hlᵢ & Hlₛ & H● & Hreqs')" "Hclose".
        iModIntro.
        destruct (decide (n' = n)) as [-> | Hneq].
        * (* Contrary to the prophecy, the CmpXchg succeeds *)
          wp_cmpxchg_suc.
          iIntros "!> %vs' -> _ //".
        * wp_cmpxchg_fail.
          iIntros "!> %vs' -> _".
          inv Hres.
          (* The registry must still contain out linearization request *)
          iCombine "H● H◯" gives %Hagree%registry_agree.
          (* Consider which state our helping request is in*)
          iPoseProof (big_sepL_lookup_acc _ _ _ _ Hagree with "Hreqs'") as "[[Hlin | [[%Hne' _] | Hγₜ']] Hrest]".
          { (* It has been fulfilled by a writer as expected *)
            (* We recombine the reduced right refinement with our left refinement *)
            iApply (refines_combine with "[-Hlin] Hlin").
            iMod ("Hclose" with "[-]") as "_".
            { iFrame. iApply "Hrest". iFrame. }
            rel_pures_l.
            rel_values. }
          { (* Our request is still pending *)
            (* This is impossible, as the value stored in the cell is what was prophecized *)
            simplify_eq. }
          { (* We have returned *)
            (* This is impossible, as we still own the token. There cannot be another copy in the invariant *)
            iExFalso. iApply (token_exclusive with "Hγₜ Hγₜ'"). }
    - (* The prophecy predicts an ill-typed return value from the CmpXchg *)
      (* This is impossible, so we just reduce the implementation to arrive at a contradiction *)
      iIntros "!> !> Hlᵢ".
      iMod ("Hclose" with "[$]") as "_".
      rel_apply_l refines_resolveatomic_l.
      { done. }
      iInv rwcasN as (n' reqs') "(Hlᵢ & Hlₛ & H● & Hreqs')" "Hclose".
      iExists _. iFrame.
      iModIntro.
      destruct (decide (n' = n)) as [-> | Hne].
      + wp_cmpxchg_suc.
        iIntros "!> %vs' -> _ //".
      + wp_cmpxchg_fail.
        iIntros "!> %vs' -> _ //".
  Qed.

  Lemma rwcas_refinement : 
    ⊢ REL wf_rwcas << atomic_rwcas : () → (lrel_int → ()) * (() → lrel_int).
  Proof.
    iApply refines_arrow_val.
    iModIntro. iIntros (? ?) "_"; simplify_eq/=.
    rel_rec_l. rel_rec_r.
    rel_alloc_l lᵢ as "Hlᵢ".
    rel_alloc_r lₛ as "Hlₛ".
    (* Establish the invariant with an empty registry *)
    iMod (own_alloc (● map_seq O (to_agree <$> []))) as "[%γ H●]".
    { by apply auth_auth_valid. }
    iAssert (rwcas_inv γ lᵢ lₛ) with ("[Hlᵢ Hlₛ H●]") as "Hinv".
    { iExists 0. iFrame. by rewrite /registry_inv. }
    iMod (inv_alloc rwcasN with "[Hinv]") as "#Hinv".
    { done. }

    do 4 rel_pure_r. do 4 rel_pure_l.
    iApply refines_pair.
    - iApply refines_arrow_val.
      iModIntro. iIntros (? ?) "(%v & -> & ->)". rel_seq_l; rel_seq_r.
      iApply (write_refinement with "Hinv").
    - iApply refines_arrow_val.
      iModIntro. iIntros (? ?) "_". rel_seq_l; rel_seq_r.
      iApply (read_refinement with "Hinv").
  Qed.
          
End wf.
