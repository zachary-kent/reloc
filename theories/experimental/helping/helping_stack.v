(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Fine-grained stack with helping.
Based on the case study <https://iris-project.org/pdfs/2017-case-study-concurrent-stacks-with-helping.pdf> *)
(** This demonstrates how to do /helping/ in ReLoC/Iris. Note that for
this proof we cannot stay inside the ReLoC and we have to unfold some
stuff to get to the actual model of logical relations. The initial
version of this code was written togethe witr Amin Timany around 2017.
Upon suggestion by Lars Birkedal I've removed the "mailbox"
indirection, but made the proof (almost) abstract in the theory of
offers. As a result, the only two places where we abandon ReLoC specs
are:

  -- The `revoke_offer_l` lemma which specifies the symbolic execution
     rule for `revoke_offer` specifialized to the case of helping. In
     order to prove this lemma we have to unfold the model of the REL
     proposition.

  -- In the proof of the pop refinement we have to symbolic execute
     the coarse grained push operation (to actually simulate the
     helping); this is done using the tp_ tactics and not the usual
     ReLoC specification.
*)
From iris.algebra Require Import auth gmap agree list excl.
From iris.base_logic.lib Require Import auth.
From reloc Require Export reloc experimental.helping.offers.
From reloc Require Import lib.list.
From reloc.examples.stack Require Import CG_stack refinement.

(** * Source code *)
Definition pop_st_no_offer : val := λ: "r" "mb" "pop",
  match: !"r" with
      NONE => NONE
    | SOME "l" =>
      let: "pair" := !"l" in
      if: CAS "r" (SOME "l") (Snd "pair")
      then SOME (Fst "pair")
      else "pop" "r" "mb"
  end.

Definition pop_st : val := rec: "pop" "r" "mb" :=
  match: !"mb" with
    NONE =>
    (* there are no offers *) pop_st_no_offer "r" "mb" "pop"
  | SOME "off" =>
    (* trying to accept an offer instead of doing an actual POP *)
    match: take_offer "off" with
      NONE => (* did not succeed on accepting the offer *)
      pop_st_no_offer "r" "mb" "pop"
    | SOME "x" => SOME "x"
    end
  end.

Definition push_st : val := rec: "push" "r" "mb" "x" :=
  let: "off" := mk_offer "x" in
  "mb" <- SOME "off";;
  match: revoke_offer "off" with
    NONE => (* the offer was successfully taken *) #()
  | SOME "x" =>
    (* nobody took the offer  *)
    let: "tail" := !"r" in
    let: "hd" := SOME (ref ("x", "tail")) in
    if: CAS "r" "tail" "hd"
    then #()
    else "push" "r" "mb" "x"
  end.

Definition mk_stack : val :=  λ: <>,
  (* mailbox which will contain offered elements *)
  let: "mb" := ref NONE in
  (* the stack itself *)
  let: "r" := ref NONE in
  (λ: <>, pop_st "r" "mb",
   λ: "x", push_st "r" "mb" "x").

(** The coarse-grained version; we will prove that stack with helping refines it. *)
Definition CG_mkstack : val := λ: <>,
  let: "st" := CG_new_stack #() in
  (λ: <>, CG_locked_pop "st", λ: "x", CG_locked_push "st" "x").


(** * Logical theory of an offer registry *)
(** We will use an "offer registery". It associates for each offer a
value that is being offered and a potential thread with the
continuation that accepts the offer, if it is present. *)

Canonical Structure ectx_itemO := leibnizO ectx_item.
(* TODO: move !! *)
Canonical Structure ref_idO := leibnizO ref_id.
Global Instance ref_id_inhabited : Inhabited ref_id.
Proof. split. apply (RefId 0 []). Qed.

Definition offerReg := gmap loc (val * gname * ref_id).
Definition offerRegR :=
  gmapUR loc (agreeR (prodO valO (prodO gnameO ref_idO))).

Class offerRegPreG Σ := OfferRegPreG {
  offerReg_inG :> authG Σ offerRegR
}.

Definition offerize (x : (val * gname * ref_id)) :
  (agreeR (prodO valO (prodO gnameO ref_idO))) :=
  match x with
  | (v, γ, k) => to_agree (v, (γ, k))
  end.

Definition to_offer_reg : offerReg -> offerRegR := fmap offerize.

Lemma to_offer_reg_valid N : ✓ to_offer_reg N.
Proof.
  intros l. rewrite lookup_fmap. case (N !! l); simpl; try done.
  intros [[v γ] k]; simpl. done.
Qed.

Section offerReg_rules.
  Context `{!offerRegPreG Σ, !offerG Σ}.

  Lemma offerReg_alloc (o : loc) (v : val) (γ : gname)
    (k : ref_id) (γo : gname) (N : offerReg)  :
    N !! o = None →
    own γo (● to_offer_reg N)
    ==∗ own γo (● to_offer_reg (<[o:=(v, γ, k)]> N))
      ∗ own γo (◯ {[o := offerize (v, γ, k)]}).
  Proof.
    iIntros (HNo) "HN".
    iMod (own_update with "HN") as "[HN Hfrag]".
    { eapply auth_update_alloc.
      eapply (alloc_singleton_local_update _ o (to_agree (v, (γ, k)))); try done.
      by rewrite /to_offer_reg lookup_fmap HNo. }
    iFrame. by rewrite /to_offer_reg fmap_insert.
  Qed.

  Lemma offerReg_frag_lookup (o : loc) (v : val) (γ : gname)
    k (γo : gname) (N : offerReg)  :
    own γo (● to_offer_reg N)
    -∗ own γo (◯ {[o := to_agree (v, (γ, k))]})
    -∗ ⌜N !! o = Some (v, γ, k)⌝.
  Proof.
    iIntros "HN Hfrag".
    iDestruct (own_valid_2 with "HN Hfrag") as %Hfoo.
    apply auth_both_valid_discrete in Hfoo.
    simpl in Hfoo. destruct Hfoo as [Hfoo _].
    iAssert (⌜✓ ((to_offer_reg N) !! o)⌝)%I as %Hvalid.
    { iDestruct (own_valid with "HN") as %HNvalid.
      iPureIntro. revert HNvalid.
      rewrite auth_auth_valid. done. }
    iPureIntro.
    revert Hfoo.
    rewrite singleton_included_l=> -[av []].
    revert Hvalid.
    rewrite /to_offer_reg !lookup_fmap.
    case: (N !! o)=> [av'|] Hvalid; last by inversion 1.
    intros Hav.
    rewrite -(inj Some _ _ Hav).
    rewrite Some_included_total.
    destruct av' as [[??]?]. simpl.
    rewrite to_agree_included.
    fold_leibniz.
    intros. by simplify_eq.
  Qed.

  Lemma offerReg_lookup_frag (o : loc) (v : val) (γ : gname)
    (k : ref_id) (γo : gname) (N : offerReg) :
    N !! o = Some (v, γ, k) →
    own γo (● to_offer_reg N)
    ==∗ own γo (◯ {[o := to_agree (v, (γ, k))]})
      ∗ own γo (● to_offer_reg N).
  Proof.
    iIntros (HNo) "Hown".
    iMod (own_update with "[Hown]") as "Hown".
    { eapply (auth_update (to_offer_reg N) ∅).
      eapply (op_local_update_discrete _ ∅ {[o := to_agree (v, (γ, k))]}).
      intros. intros i. destruct (decide (i = o)); subst; rewrite lookup_op.
      + rewrite lookup_singleton lookup_fmap HNo.
        rewrite -Some_op.
        rewrite Some_valid.
        rewrite agree_idemp. done.
      + rewrite lookup_singleton_ne; eauto.
        rewrite left_id.
        done.
    }
    { (** TODO: this is silly *)
      assert (RightId (≡) (◯ ∅ : authUR offerRegR) (⋅)).
      { apply (@ucmra_unit_right_id (authUR offerRegR)). }
      rewrite right_id. iFrame "Hown". }
    iDestruct "Hown" as "[Ho Hown]".
    rewrite right_id. iFrame.
    assert ({[o := to_agree (v, (γ, k))]} ⋅ to_offer_reg N ≡ to_offer_reg N) as Hfoo.
    { intro i.
      rewrite /to_offer_reg lookup_merge !lookup_fmap.
      destruct (decide (i = o)); subst.
      + rewrite HNo lookup_singleton /=.
        rewrite -Some_op.
        apply Some_proper.
        symmetry. apply agree_included.
        by apply to_agree_included.
      + rewrite lookup_singleton_ne; eauto.
        by rewrite left_id. }
    by rewrite Hfoo.
  Qed.

  (** The invariant that we will have. *)
  Definition offerInv `{!relocG Σ} (N : offerReg) (st' : val) : iProp Σ :=
    ([∗ map] l ↦ w ∈ N,
     match w with
     | (v,γ,k) => is_offer γ l
                             (refines_right k (CG_locked_push st' (of_val v))%E)
                             (refines_right k #())
     end)%I.

  Lemma offerInv_empty `{!relocG Σ} (st' : val) : ⊢ offerInv ∅ st'.
  Proof. by rewrite /offerInv big_sepM_empty. Qed.

  Lemma offerInv_excl `{!relocG Σ} (N : offerReg) (st' : val) (o : loc) γ P Q :
    offerInv N st' -∗ is_offer γ o P Q -∗ ⌜N !! o = None⌝.
  Proof.
    rewrite /offerInv. iIntros "HN Ho".
    iAssert (⌜is_Some (N !! o)⌝ → False)%I as %Hbaz.
    {
      iIntros ([[[? ?] ?] HNo]).
      rewrite (big_sepM_lookup _ N o _ HNo).
      iApply (is_offer_exclusive with "HN Ho").
    }
    iPureIntro. revert Hbaz. case: (N !! o)=> [av'|]; naive_solver.
  Qed.

End offerReg_rules.

(* TODO: this goes in Iris *)
Section sep_list2.
  Context `{!relocG Σ} {A B : Type}.
  Implicit Types Φ Ψ : nat → A → B → iProp Σ.

  Lemma big_sepL2_nil_inv_l Φ l2 :
    ([∗ list] k↦y1;y2 ∈ []; l2, Φ k y1 y2) -∗ ⌜l2 = []⌝.
  Proof.
    rewrite big_sepL2_alt bi.and_elim_l /= -length_zero_iff_nil.
    by apply bi.pure_mono.
  Qed.
  Lemma big_sepL2_nil_inv_r Φ l1 :
    ([∗ list] k↦y1;y2 ∈ l1; [], Φ k y1 y2) -∗ ⌜l1 = []⌝.
  Proof.
    rewrite big_sepL2_alt bi.and_elim_l /= length_zero_iff_nil.
    by apply bi.pure_mono.
  Qed.

End sep_list2.

(** * Refinement proof *)
Section refinement.
  Context `{!relocG Σ, !offerRegPreG Σ, !offerG Σ}.

  Implicit Type A : lrel Σ.

  Definition stackN := nroot .@ "stacked".

  (** First we have the revoke_offer symbolic execution rule specialized for helping.
      This is also the only place where we need to unfold the definition of the refinement proposition. *)
  Lemma revoke_offer_l γ off E K (v : val) e1 e2 A :
    offer_token γ -∗
    (∀ k, refines_right k e1  ={E}[⊤]▷=∗
      ▷ is_offer γ off (refines_right k e1) (refines_right k e2) ∗
      ▷ (is_offer γ off (refines_right k e1) (refines_right k e2) -∗
           ((REL fill K (of_val NONEV) << e2 @ E : A)
         ∧ (REL fill K (of_val $ SOMEV v) << e1 @ E : A)))) -∗
    REL fill K (revoke_offer (v, #off)%V) << e1 @ E : A.
  Proof.
    iIntros "Hγ Hlog".
    iApply refines_split.
    iIntros (k) "Hk".
    iMod ("Hlog" with "Hk") as "Hlog".
    iApply refines_wp_l.
    wp_apply (wp_revoke_offer with "Hγ [-]").
    iNext. iMod "Hlog" as "[Hoff Hcont]". iModIntro.
    iFrame "Hoff". iNext. iSplit.
    - iIntros "Hoff". iDestruct ("Hcont" with "Hoff") as "[Hcont _]".
      iIntros "Hk". iApply refines_left_fupd.
      iApply (refines_combine with "Hcont Hk").
    - iIntros "Hoff". iDestruct ("Hcont" with "Hoff") as "[_ Hcont]".
      iIntros "Hk". iApply refines_left_fupd.
      iApply (refines_combine with "Hcont Hk").
  Qed.

  (** We will also use the following instances for splitting and
  compining read-only pointsto permissions. *)
  Local Instance ro_pointsto_fromand (l : loc) (w : val) :
    FromSep (∃ q, l ↦{q} w) (∃ q, l ↦{q} w) (∃ q, l ↦{q} w).
  Proof.
    rewrite /FromSep. iIntros "[$ _]".
  Qed.
  Local Instance ro_pointsto_intoand (l : loc) (w : val) :
    IntoSep (∃ q, l ↦{q} w) (∃ q, l ↦{q} w) (∃ q, l ↦{q} w).
  Proof.
    rewrite /IntoSep /=. iDestruct 1 as (q) "[H1 H2]".
    iSplitL "H1"; eauto with iFrame.
  Qed.

  (** Then we have definitions and lemmas that we use for actually
  liking the contents of the two stacks together *)
  Definition olocO := leibnizO (option loc).

  Definition oloc_to_val (ol: option loc) : val :=
    match ol with
    | None => NONEV
    | Some loc => SOMEV (#loc)
    end.

  Local Instance oloc_to_val_inj : Inj (=) (=) oloc_to_val.
  Proof. intros [|][|]; simpl; congruence. Qed.

  Fixpoint stack_contents (ol : option loc) (ls : list val) :=
    match ol,ls with
    | None,[] => True
    | Some l,(h::t) =>
      ∃ (ol : option loc),
      ∃ q, l ↦{q} (h, oloc_to_val ol) ∗ stack_contents ol t
    | _,_ => False
    end%I.

  Existing Instance istk_fromand.
  Existing Instance istk_intoand.
  Local Instance stack_contents_intoand (istk : option loc) (ls : list val) :
    IntoSep (stack_contents istk ls) (stack_contents istk ls) (stack_contents istk ls).
  Proof.
    rewrite /IntoSep /=.
    revert istk. induction ls as [|h ls]; intros istk; simpl.
    - destruct istk; eauto.
    - destruct istk; last by eauto. iDestruct 1 as (z1 q) "[Histk Hc]".
      rewrite IHls. iDestruct "Hc" as "[Hc1 Hc2]". iDestruct "Histk" as "[Histk1 Histk2]".
      iSplitL "Hc1 Histk1"; iExists _, (q/2)%Qp; by iFrame.
  Qed.

  Lemma stack_contents_agree istk ls ls' :
    stack_contents istk ls -∗ stack_contents istk ls' -∗ ⌜ls = ls'⌝.
  Proof.
    revert istk ls'. induction ls as [|h ls]; intros istk ls'; simpl.
    - destruct istk; eauto.
      destruct ls' as [|h' ls']; simpl; eauto.
    - destruct istk; last eauto.
      iDestruct 1 as (z q) "[Histk Hls]".
      destruct ls' as [|h' ls']; simpl; eauto.
      iDestruct 1 as (z' q') "[Histk' Hls']".
      iDestruct (gen_heap.mapsto_agree with "Histk' Histk") as %Hfoo. simplify_eq/=.
      iDestruct (IHls with "Hls Hls'") as %Hbar. simplify_eq/=.
      eauto.
  Qed.

  (** ** The main invariant that we will use for the proof *)
  Definition stackInv A oname (st mb : loc) (st' : val) : iProp Σ :=
    (∃ ol (N : offerReg) ls1 ls2,
       st ↦ oloc_to_val ol
     ∗ stack_contents ol ls1
     ∗ is_stack st' ls2
     ∗ ([∗ list] v1;v2 ∈ ls1;ls2, A v1 v2)
     ∗ (mb ↦ NONEV      (* the mailbox is either empty or contains an offer that is in the registry *)
        ∨ (∃ (l : loc) v1 v2 γ k,
              A v1 v2
            ∗ mb ↦ SOMEV (v1, #l)
            ∗ ⌜N !! l = Some (v2, γ, k)⌝))
     ∗ own oname (● to_offer_reg N)
     ∗ offerInv N st')%I.

  (** ** The proof itself *)

  (* First the case where no offers is accepted *)
  Lemma pop_no_helping_refinement A γo st st' mb :
    inv stackN (stackInv A γo st mb st') -∗
    (REL pop_st #st #mb
       <<
      CG_locked_pop st' : () + A) -∗
    REL pop_st_no_offer #st #mb pop_st
    <<
    CG_locked_pop st' : () + A.
  Proof.
    iIntros "#Hinv IH". rel_rec_l. rel_pures_l.
    rel_load_l_atomic.
    iInv stackN as (ol N ls1 ls2) "(Hol & Hst1 & Hst2 & HA & Hmb & Hown & HN)" "Hcl".
    iModIntro. iExists _; iFrame. iNext. iIntros "Hol".
    destruct ls1 as [|h1 ls1].
    - iSimpl in "Hst1".
      destruct ol; first by eauto with iFrame.
      rel_pures_l.
      rewrite (big_sepL2_nil_inv_l _ ls2). iDestruct "HA" as %->.
      simpl. rel_pures_l.
      rel_apply_r (refines_CG_pop_fail_r with "Hst2").
      iIntros "Hst2". iMod ("Hcl" with "[-IH]") as "_".
      { iNext. iExists None,_,[],_. simpl; iFrame.
        by rewrite big_sepL2_nil. }
      rel_values. iExists _,_. eauto with iFrame.
    - iDestruct "Hst1" as "[Hst1 Hst1']".
      iSimpl in "Hst1". destruct ol as [l|]; last by eauto with iFrame.
      iDestruct "Hst1" as (ol q) "[[Hl Hl'] [Hol' Hol2]]".
      rel_pures_l. iMod ("Hcl" with "[-Hl IH Hst1' Hol2]") as "_".
      { iNext. iExists (Some l),_,(h1::ls1),_. iFrame.
        simpl. eauto with iFrame. }
      rel_load_l. rel_pures_l. iClear "Hl".
      rel_cmpxchg_l_atomic.
      iInv stackN as (ol2 N' ls1' ls2') "(Hol & Hst1 & Hst2 & HA & Hmb & Hown & HN)" "Hcl".
      iModIntro. iExists _. iFrame "Hol". iSplit.
      + iIntros (?). iNext.
        iIntros "Hol". rel_pures_l.
        iMod ("Hcl" with "[-IH]").
        { iNext. iExists _,_,_,_. by iFrame. }
        iApply "IH".
      + iIntros (?). iNext.
        iIntros "Hol". rel_pures_l.
        assert (ol2 = Some l) as ->.
        { destruct ol2; by simplify_eq/=. }
        iDestruct (stack_contents_agree with "Hst1 Hst1'") as %->.
        rewrite big_sepL2_cons_inv_l.
        iDestruct "HA" as (h2 ls2'' ->) "[#Hh HA]".
        rel_apply_r (refines_CG_pop_suc_r with "Hst2").
        iIntros "Hst2".
        iMod ("Hcl" with "[-]").
        { iNext. iExists _,_,_,_. by iFrame. }
        rel_values. iExists _,_. eauto with iFrame.
  Qed.

  Lemma pop_refinement A γo st st' mb :
    inv stackN (stackInv A γo st mb st') -∗
    REL pop_st #st #mb
      <<
    CG_locked_pop st' : () + A.
  Proof.
    iIntros "#Hinv".
    iLöb as "IH".
    rel_rec_l. rel_pures_l.
    rel_load_l_atomic.
    iInv stackN as (ol N ls1 ls2) "(Hol & Hst1 & Hst2 & HA & Hmb & HNown & HN)" "Hcl".
    iDestruct "Hmb" as "[Hmb | Hmb]".
    - (* NO OFFER *)
      iModIntro. iExists _; iFrame.
      iNext. iIntros "Hmb".
      rel_pures_l.
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _, _, _, _; by iFrame. }
      iApply (pop_no_helping_refinement with "Hinv IH").
    - (* YES OFFER *)
      iDestruct "Hmb" as (l v1 v2 γ k) "(#Hv & >Hmb & >HNl)".
      iDestruct "HNl" as %HNl.
      rewrite /offerInv big_sepM_lookup_acc; eauto. iSimpl in "HN".
      iDestruct "HN" as "[HNl HN]".
      iMod "HNown".
      iMod (offerReg_lookup_frag with "HNown") as "[#Hlown HNown]"; eauto.
      iModIntro. iExists _; iFrame.
      iNext. iIntros "Hmb".
      iMod ("Hcl" with "[-Hlown IH]") as "_".
      { iNext. iExists _, _, _, _; iFrame.
        iSplitL "Hmb".
        - iRight. iExists _, _, _, _, _.
          eauto with iFrame.
        - by iApply "HN". }

      rel_pures_l. rel_apply_l (take_offer_l _ ).
      iInv stackN as (ol' N' ls1' ls2') "(Hol & Hst1 & Hst2 & HA & Hmb & HNown & HN)" "Hcl".
      simplify_eq/=.
      iMod "HNown".
      iDestruct (offerReg_frag_lookup with "HNown Hlown") as %?.
      rewrite /offerInv (big_sepM_lookup_acc _ _ l); eauto. iSimpl in "HN".
      iDestruct "HN" as "[HNl HN]". iModIntro.
      iFrame "HNl". iNext. iSplit.
      +  (* Did not manage to accept an offer *)
        iIntros "HNl".
        iMod ("Hcl" with "[-IH]") as "_".
        { iNext. iExists _,_,_,_. iFrame.
          by iApply "HN". }
        rel_pures_l.
        iApply (pop_no_helping_refinement with "Hinv IH").
      + (* An offer was accepted *)
        iIntros "Hk Hoff". rel_pures_l.
        iDestruct "Hst2" as (st2l lk ->) "[Hlk Hst2]".
        tp_rec k. tp_pures k. tp_rec k.
        unlock is_locked_r. iDestruct "Hlk" as (lk' ->) "Hl".
        (* TODO: make all the tp_ tactics work without the need for an explicit Fupd *)
        tp_cmpxchg_suc k.
        tp_pures k. tp_rec k. tp_pures k.
        tp_load k. tp_pures k.
        tp_store k. tp_pures k.
        tp_rec k. tp_store k.
        iSpecialize ("Hoff" with "Hk").
        iSpecialize ("HN" with "Hoff").

        rel_apply_r (refines_CG_pop_suc_r with "[Hst2 Hl]").
        { iExists st2l,#lk'. rewrite /is_locked_r. by eauto with iFrame. }
        iIntros "Hst2".
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists _,_,_,_. by eauto with iFrame. }
        rel_values. iModIntro. iExists v1,v2.
        iRight. repeat iSplit; eauto with iFrame.
  Qed.

  Lemma push_refinement A γo st st' mb h1 h2 :
    inv stackN (stackInv A γo st mb st') -∗
    A h1 h2 -∗
    REL push_st #st #mb h1
      <<
    CG_locked_push st' h2 : ().
  Proof.
    iIntros "#Hinv #Hh".
    iLöb as "IH".
    rel_rec_l.
    rel_pures_l.
    rel_apply_l mk_offer_l. iIntros (γ off) "Hoff Htok".
    rel_pures_l.
    rel_store_l_atomic. (* we update the mailbox and store the offer in the registry *)
    iInv stackN as (ol N ls1 ls2) "(Hol & Hst1 & Hst2 & HA & Hmb & HNown & HN)" "Hcl".
    iModIntro.
    (* first we need to show that mb is allocated / owned *)
    iAssert (∃ v, ▷ mb ↦ v)%I with "[Hmb]" as (v) "Hmb".
    { iDestruct "Hmb" as "[Hmb | Hmb]".
      - iExists NONEV; eauto.
      - iDestruct "Hmb" as (l m1 m2 γ' k) "(Hm & Hmb & ?)".
        iExists (SOMEV (m1, #l)); eauto. }
    iExists _; iFrame; iNext.
    iIntros "Hmb".

    rel_pures_l.
    rel_apply_l (revoke_offer_l with "Htok").
    iIntros (k) "Hk". iSpecialize ("Hoff" with "Hk").
    iDestruct (offerInv_excl with "HN Hoff") as %?.
    iMod (offerReg_alloc off h2 γ k with "HNown") as "[HNown #Hfrag]"; eauto.
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_,_,_; iFrame.
      iSplitL "Hmb".
      - iRight. iExists off, h1, h2, _, _. iFrame "Hmb Hh".
        iPureIntro. by rewrite lookup_insert.
      - rewrite /offerInv big_sepM_insert; eauto with iFrame. }
    iModIntro. iNext.
    iInv stackN as (ol' N' ls1' ls2') "(Hol & Hst1 & Hst2 & HA & Hmb & HNown & HN)" "Hcl".
    simplify_eq/=.
    iMod "HNown". iModIntro.
    iDestruct (offerReg_frag_lookup with "HNown Hfrag") as %Hfoo.
    rewrite /offerInv.
    (* TODO: separate lemma *)
    rewrite (big_sepM_lookup_acc _ N'); eauto.
    iDestruct "HN" as "[$ HN]".
    iNext. iIntros "Hoff". iSplit.
    - (* The offer was already accepted *)
      iSpecialize ("HN" with "Hoff").
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_,_,_; iFrame. }
      rel_pures_l. rel_values.
    - (* The offer has been successfully revoked. We have to do the actual push. *)
      iSpecialize ("HN" with "Hoff").
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_,_,_; iFrame. }
      clear.
      rel_pures_l. rel_load_l_atomic.
      iInv stackN as (ol N ls1 ls2) "(Hol & Hst1 & Hst2 & HA & Hmb & HNown & HN)" "Hcl".
      iModIntro. iExists _. iFrame. iNext. iIntros "Hol".

      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_,_,_; iFrame. }

      rel_pures_l. rel_alloc_l new as "Hnew". rel_pures_l.

      rel_cmpxchg_l_atomic; first by destruct ol.
      iInv stackN as (ol' N' ls1' ls2') "(Hol & Hst1 & Hst2 & HA & Hmb & HNown & HN)" "Hcl".
      iModIntro. iExists _. iFrame "Hol". iSplit.
      + iIntros (?). iNext. iIntros "Hol".
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists _,_,_,_; by iFrame. }
        rel_pures_l. iApply "IH".
      + iIntros (?); simplify_eq/=. iNext.
        iIntros "Hol".
        rel_apply_r (refines_CG_push_r with "Hst2").
        iIntros "Hst2".
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists (Some new),_,(h1::ls1'),_; iFrame.
          simpl. by eauto with iFrame. }
        rel_pures_l. rel_values.
  Qed.

  Lemma refinement :
    ⊢ REL mk_stack << CG_mkstack : ∀ A, (() → () + A) * (A → ()).
  Proof.
    rel_values. iModIntro. iIntros (A). iModIntro.
    iIntros (? ?) "[-> ->]".
    rel_rec_r. rel_pures_r. rel_rec_r.
    rel_alloc_r st' as "Hst'". rel_pures_r.
    rel_apply_r refines_newlock_r. iIntros (lk) "Hlk".
    rel_pure_r. rel_pure_r.  rel_pure_r.  rel_pure_r.  rel_pure_r.
    rel_rec_l. rel_pures_l.
    rel_alloc_l mb as "Hmb". rel_pures_l.
    rel_alloc_l st as "Hst". do 4 rel_pure_l. (*XXX: doing rel_pures_l reduces too much *)
    iMod (own_alloc (● to_offer_reg ∅ : authR offerRegR)) as (γo) "Hor".
    { apply auth_auth_valid. apply to_offer_reg_valid. }
    iMod (inv_alloc stackN _ (stackInv A γo st mb (#st', lk)%V) with "[-]") as "#Hinv".
    { iNext. unfold stackInv.
      iExists None, _, [],[]. iFrame.
      iSplit; eauto.
      - rewrite /is_stack. iExists _,_. eauto with iFrame.
      - iSplit; first done. iApply offerInv_empty. }
    iApply refines_pair; last first.
    (* * Push refinement *)
    { rel_arrow_val. iIntros (h1 h2) "#Hh"; simplify_eq/=.
      rel_pures_l. rel_pures_r.
      iApply (push_refinement with "Hinv Hh"). }
    (* * Pop refinement *)
    { rel_arrow_val. iIntros (? ?) "[% %]"; simplify_eq/=.
      rel_pures_l. rel_pures_r.
      iApply (pop_refinement with "Hinv"). }
  Qed.

End refinement.
