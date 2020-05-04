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
From reloc Require Import examples.stack.CG_stack lib.list.

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
Definition offerReg := gmap loc (val * gname * nat * (list ectx_item)).
Definition offerRegR :=
  gmapUR loc (agreeR (prodO valO (prodO gnameO (prodO natO (listO ectx_itemO))))).

Class offerRegPreG Σ := OfferRegPreG {
  offerReg_inG :> authG Σ offerRegR
}.

Definition offerize (x : (val * gname * nat * (list ectx_item))) :
  (agreeR (prodO valO (prodO gnameO (prodO natO (listO ectx_itemO))))) :=
  match x with
  | (v, γ, n, K) => to_agree (v, (γ, (n, K)))
  end.

Definition to_offer_reg : offerReg -> offerRegR := fmap offerize.

Lemma to_offer_reg_valid N : ✓ to_offer_reg N.
Proof.
  intros l. rewrite lookup_fmap. case (N !! l); simpl; try done.
  intros [[[v γ] n] K]; simpl. done.
Qed.

Section offerReg_rules.
  Context `{!offerRegPreG Σ, !offerG Σ}.

  Lemma offerReg_alloc (o : loc) (v : val) (γ : gname)
    (j : nat) (K : list ectx_item) (γo : gname) (N : offerReg)  :
    N !! o = None →
    own γo (● to_offer_reg N)
    ==∗ own γo (● to_offer_reg (<[o:=(v, γ, j, K)]> N))
      ∗ own γo (◯ {[o := offerize (v, γ, j, K)]}).
  Proof.
    iIntros (HNo) "HN".
    iMod (own_update with "HN") as "[HN Hfrag]".
    { eapply auth_update_alloc.
      eapply (alloc_singleton_local_update _ o (to_agree (v, (γ, (j, K))))); try done.
      by rewrite /to_offer_reg lookup_fmap HNo. }
    iFrame. by rewrite /to_offer_reg fmap_insert.
  Qed.

  Lemma offerReg_frag_lookup (o : loc) (v : val) (γ : gname)
    (j : nat) (K : list ectx_item) (γo : gname) (N : offerReg)  :
    own γo (● to_offer_reg N)
    -∗ own γo (◯ {[o := to_agree (v, (γ, (j, K)))]})
    -∗ ⌜N !! o = Some (v, γ, j, K)⌝.
  Proof.
    iIntros "HN Hfrag".
    iDestruct (own_valid_2 with "HN Hfrag") as %Hfoo.
    apply auth_both_valid in Hfoo.
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
    destruct av' as [[[??]?]?]. simpl.
    rewrite to_agree_included.
    fold_leibniz.
    intros. by simplify_eq.
  Qed.

  Lemma offerReg_lookup_frag (o : loc) (v : val) (γ : gname)
    (j : nat) (K : list ectx_item) (γo : gname) (N : offerReg) :
    N !! o = Some (v, γ, j, K) →
    own γo (● to_offer_reg N)
    ==∗ own γo (◯ {[o := to_agree (v, (γ, (j, K)))]})
      ∗ own γo (● to_offer_reg N).
  Proof.
    iIntros (HNo) "Hown".
    iMod (own_update with "[Hown]") as "Hown".
    { eapply (auth_update (to_offer_reg N) ∅).
      eapply (op_local_update_discrete _ ∅ {[o := to_agree (v, (γ, (j, K)))]}).
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
    assert ({[o := to_agree (v, (γ, (j, K)))]} ⋅ to_offer_reg N ≡ to_offer_reg N) as Hfoo.
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
     | (v,γ,j,K) => is_offer γ l
                             (j ⤇ fill K (CG_locked_push st' (of_val v))%E)
                             (j ⤇ fill K #())
     end)%I.

  Lemma offerInv_empty `{!relocG Σ} (st' : val) : ⊢ offerInv ∅ st'.
  Proof. by rewrite /offerInv big_sepM_empty. Qed.

  Lemma offerInv_excl `{!relocG Σ} (N : offerReg) (st' : val) (o : loc) γ P Q :
    offerInv N st' -∗ is_offer γ o P Q -∗ ⌜N !! o = None⌝.
  Proof.
    rewrite /offerInv. iIntros "HN Ho".
    iAssert (⌜is_Some (N !! o)⌝ → False)%I as %Hbaz.
    {
      iIntros ([[[[? ?] ?] ?] HNo]).
      rewrite (big_sepM_lookup _ N o _ HNo).
      iApply (is_offer_exclusive with "HN Ho").
    }
    iPureIntro. revert Hbaz. case: (N !! o)=> [av'|]; naive_solver.
  Qed.

End offerReg_rules.

(** * Refinement proof *)
Section refinement.
  Context `{!relocG Σ, !offerRegPreG Σ, !offerG Σ}.

  Implicit Type A : lrel Σ.

  Definition stackN := nroot .@ "stacked".

  (** First we have the revoke_offer symbolic execution rule specialized for helping.
      This is also the only place where we need to unfold the definition of the refinement proposition. *)
  Lemma revoke_offer_l γ off E K (v : val) e1 e2 A :
    offer_token γ -∗
    (∀ j K', (j ⤇ fill K' e1)  ={E, ⊤, E}▷=∗
      ▷ is_offer γ off (j ⤇ fill K' e1) (j ⤇ fill K' e2) ∗
      ▷ (is_offer γ off (j ⤇ fill K' e1) (j ⤇ fill K' e2) -∗
           ((REL fill K (of_val NONEV) << e2 @ E : A)
         ∧ (REL fill K (of_val $ SOMEV v) << e1 @ E : A)))) -∗
    REL fill K (revoke_offer (v, #off)%V) << e1 @ E : A.
  Proof.
    iIntros "Hγ Hlog".
    rewrite {3}refines_eq /refines_def.
    iIntros (j K') "#Hs Hj".
    iMod ("Hlog" with "Hj") as "Hlog".
    iModIntro. iApply wp_bind. (* TODO: why do we have to use wp_bind here? *)
    wp_apply (wp_revoke_offer with "Hγ [-]").
    iNext. iMod "Hlog" as "[Hoff Hcont]". iModIntro.
    iFrame "Hoff". iNext. iSplit.
    - iIntros "Hoff". iDestruct ("Hcont" with "Hoff") as "[Hcont _]".
      rewrite refines_eq. by iApply "Hcont".
    - iIntros "Hoff". iDestruct ("Hcont" with "Hoff") as "[_ Hcont]".
      rewrite refines_eq. by iApply "Hcont".
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

  (** This will be the type of the stack linking predicate... *)
  Local Notation D := (olocO -d> valO -d> iPropO Σ).
  (** .. which we compute as the following fixed point: *)
  Definition stack_link_pre (A : lrel Σ) : D → D := λ S ol v2,
    match ol return _ with
    | None => ⌜v2 = NONEV⌝
    | Some l => ∃ (h : val) (t : option loc) (h' t' : val),
                  ⌜v2 = SOMEV (h', t')⌝
                ∗ (∃ q, l ↦{q} (h, oloc_to_val t))
                ∗ A h h' ∗ ▷ S t t'
    end%I.
  Global Instance stack_link_pre_contractive A : Contractive (stack_link_pre A).
  Proof.
    intros n S1 S2 HS. solve_proper_prepare.
    repeat (first [apply HS | f_contractive | f_equiv]).
  Qed.

  Definition stack_link A := fixpoint (stack_link_pre A).

  Lemma stack_link_unfold A ol v2 :
    stack_link A ol v2 ≡
    (match ol with
     | None => ⌜v2 = NONEV⌝
     | Some l => ∃ (h : val) (t : option loc) (h' t' : val),
                   ⌜v2 = SOMEV (h', t')⌝
                 ∗ (∃ q, l ↦{q} (h, oloc_to_val t))
                 ∗ A h h' ∗ ▷ stack_link A t t'
     end%I).
  Proof. apply (fixpoint_unfold (stack_link_pre A)). Qed.

  Lemma stack_link_empty A : ⊢ stack_link A None NILV.
  Proof. rewrite stack_link_unfold; by iPureIntro. Qed.

  Lemma stack_link_cons A l h h' t t' q :
    A h h' -∗
    ▷ stack_link A t t' -∗
    l ↦{q} (h, oloc_to_val t) -∗
    stack_link A (Some l) (CONSV h' t').
  Proof.
    iIntros "Hh Ht Hl".
    rewrite (stack_link_unfold A (Some _)).
    iExists _,_,_,_. iFrame "Hh Ht". iSplit; eauto with iFrame.
  Qed.

  (** ** The main invariant that we will use for the proof *)
  Definition stackInv A oname (st st' mb : loc) (lc : val) : iProp Σ :=
    (∃ ol v2 (N : offerReg),
       is_locked_r lc false
     ∗ st ↦ oloc_to_val ol
     ∗ st' ↦ₛ v2
     ∗ stack_link A ol v2
     ∗ (mb ↦ NONEV      (* the mailbox is either empty or contains an offer that is in the registry *)
        ∨ (∃ (l : loc) v1 v2 γ j K,
              A v1 v2
            ∗ mb ↦ SOMEV (v1, #l)
            ∗ ⌜N !! l = Some (v2, γ, j, K)⌝))
     ∗ own oname (● to_offer_reg N)
     ∗ offerInv N (#st', lc))%I.

  (** ** The proof itself *)

  (* First the case where no offers is accepted *)
  Lemma pop_no_helping_refinement A γo st st' mb lk :
    inv stackN (stackInv A γo st st' mb lk) -∗
    (REL pop_st #st #mb
       <<
      CG_locked_pop (#st', lk)%V : () + A) -∗
    REL pop_st_no_offer #st #mb pop_st
    <<
    CG_locked_pop (#st', lk)%V : () + A.
  Proof.
    iIntros "#Hinv IH". rel_rec_l. rel_pures_l.
    rel_load_l_atomic.
    iInv stackN as (s1 s2 N) "(Hlk & Hst1 & Hst2 & Hrel & Hmb & HNown & HN)" "Hcl".
    iModIntro. iExists _; iFrame. iNext. iIntros "Hst1".
    rewrite stack_link_unfold.
    destruct s1 as [l|]; last first.
    - (* Stack is empty *)
      iDestruct "Hrel" as "->". iSimpl.
      rel_pures_l.
      rel_apply_r (refines_CG_pop_fail_r with "Hst2 Hlk").
      iIntros "Hst' Hlk".
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_,_. iFrame.
        iApply stack_link_empty. }
      rel_values. iModIntro. iExists #(),#().
      iLeft; repeat iSplit; eauto with iFrame.
    - iDestruct "Hrel" as (h t h' t' ->) "(Hl & #Hh & Ht)". iSimpl.
      rel_pures_l.
      iDestruct "Hl" as "[Hl Hl2]".
      iMod ("Hcl" with "[-IH Hl]") as "_".
      { iNext. iExists _,_,_. iFrame.
        iDestruct "Hl2" as (q) "Hl2".
        iApply (stack_link_cons with "Hh Ht Hl2"). }
      iDestruct "Hl" as (q) "Hl".
      rel_load_l. rel_pures_l.
      rel_cmpxchg_l_atomic.
      iInv stackN as (s1 s2 N') "(Hlk & Hst1 & Hst2 & Hrel & Hmb & HNown & HN)" "Hcl".
      iModIntro. iExists _; iFrame "Hst1". iSplit.
      + (* Going to retry *)
        iIntros (Hs1). iNext. iIntros "Hst1".
        rel_pures_l.
        iMod ("Hcl" with "[-IH]").
        { iNext. iExists _,_,_. by iFrame. }
        iApply "IH".
      + (* Going to succeed *)
        iIntros (Hs1). iNext. iIntros "Hst1".
        rel_pures_l.
        assert (s1 = Some l) as ->.
        { revert Hs1. destruct s1; simpl; congruence. }
        rewrite stack_link_unfold.
        iDestruct "Hrel" as (h1 t1 h1' t1' ->) "([Hl2 Hl3] & #Hh' & Hrel)".
        rel_apply_r (refines_CG_pop_suc_r with "Hst2 Hlk").
        iIntros "Hst' Hlk".
        iDestruct "Hl2" as (?) "Hl2".
        iDestruct (gen_heap.mapsto_agree with "Hl Hl2") as %?.
        simplify_eq/=.
        iMod ("Hcl" with "[-IH Hl Hl2]").
        { iNext. iExists _,_,_. by iFrame. }
        rel_values. iModIntro. iExists h1,h1'.
        iRight. repeat iSplit; eauto with iFrame.
  Qed.

  Lemma pop_refinement A γo st st' mb lk :
    inv stackN (stackInv A γo st st' mb lk) -∗
    REL pop_st #st #mb
      <<
    CG_locked_pop (#st', lk)%V : () + A.
  Proof.
    iIntros "#Hinv".
    iLöb as "IH".
    rel_rec_l. rel_pures_l.
    rel_load_l_atomic.
    iInv stackN as (s1 s2 N) "(>Hl & >Hst1 & >Hst2 & Hrel & Hmb & HNown & HN)" "Hcl"; simplify_eq.
    iDestruct "Hmb" as "[Hmb | Hmb]".
    - (* NO OFFER *)
      iModIntro. iExists _; iFrame.
      iNext. iIntros "Hmb".
      rel_pures_l.
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _, _, _; iFrame. }
      iApply (pop_no_helping_refinement with "Hinv IH").
    - (* YES OFFER *)
      iDestruct "Hmb" as (l v1 v2 γ j K) "(#Hv & Hmb & >HNl)".
      iDestruct "HNl" as %HNl.
      rewrite /offerInv big_sepM_lookup_acc; eauto. iSimpl in "HN".
      iDestruct "HN" as "[HNl HN]".
      iMod "HNown".
      iMod (offerReg_lookup_frag with "HNown") as "[#Hlown HNown]"; eauto.
      iModIntro. iExists _; iFrame.
      iNext. iIntros "Hmb".
      iMod ("Hcl" with "[-Hlown IH]") as "_".
      { iNext. iExists _, _, _; iFrame.
        iSplitL "Hmb".
        - iRight. iExists _, _, _, _, _, _.
          eauto with iFrame.
        - by iApply "HN". }

      rel_pures_l. rel_apply_l (take_offer_l _ ).
      iInv stackN as (s1' s2' N') "(>Hl & >Hst1 & >Hst2 & Hrel & Hmb & HNown & HN)" "Hcl"; simplify_eq.
      iMod "HNown".
      iDestruct (offerReg_frag_lookup with "HNown Hlown") as %?.
      rewrite /offerInv (big_sepM_lookup_acc _ _ l); eauto. iSimpl in "HN".
      iDestruct "HN" as "[HNl HN]". iModIntro.
      iFrame "HNl". iNext. iSplit.
      +  (* Did not manage to accept an offer *)
        iIntros "HNl".
        iMod ("Hcl" with "[-IH]") as "_".
        { iNext. iExists _,_,_. iFrame.
          by iApply "HN". }
        rel_pures_l.
        iApply (pop_no_helping_refinement with "Hinv IH").
      + (* An offer was accepted *)
        iIntros "Hj Hoff". rel_pures_l.
        tp_rec j. tp_pures j. tp_rec j.
        unlock is_locked_r. iDestruct "Hl" as (lk' ->) "Hl".
        (* TODO: make all the tp_ tactics work without the need for an explicit Fupd *)
        iApply refines_spec_ctx. iIntros "#Hρ".
        iApply fupd_refines.
        (* because we manually applied `fupd_refines`, the tactical `with_spec_ctx` doesn't work anymore *)
        tp_cmpxchg_suc j.
        tp_pures j. tp_rec j. tp_pures j.
        tp_load j. tp_pures j.
        tp_store j. tp_pures j.
        tp_rec j. tp_store j.
        iSpecialize ("Hoff" with "Hj").
        iSpecialize ("HN" with "Hoff").
        iClear "Hρ". iModIntro.

        rel_apply_r (refines_CG_pop_suc_r with "Hst2 [Hl]").
        { iExists _. by iFrame "Hl". }
        iIntros "Hst2 Hl".
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists _,_,_. by iFrame. }
        rel_values. iModIntro. iExists v1,v2.
        iRight. repeat iSplit; eauto with iFrame.
  Qed.

  Lemma push_refinement A γo st st' mb lk h1 h2 :
    inv stackN (stackInv A γo st st' mb lk) -∗
    A h1 h2 -∗
    REL push_st #st #mb h1
      <<
    CG_locked_push (#st', lk)%V h2 : ().
  Proof.
    iIntros "#Hinv #Hh".
    iLöb as "IH".
    rel_rec_l.
    rel_pures_l.
    rel_apply_l mk_offer_l. iIntros (γ off) "Hoff Htok".
    rel_pures_l.
    rel_store_l_atomic. (* we update the mailbox and store the offer in the registry *)
    iInv stackN as (s1 s2 N) "(Hl & Hst1 & Hst2 & Hrel & Hmb & HNown & HN)" "Hcl".
    iModIntro.
    (* first we need to show that mb is allocated / owned *)
    iAssert (∃ v, ▷ mb ↦ v)%I with "[Hmb]" as (v) "Hmb".
    { iDestruct "Hmb" as "[Hmb | Hmb]".
      - iExists NONEV; eauto.
      - iDestruct "Hmb" as (l m1 m2 γ' j K) "(Hm & Hmb & ?)".
        iExists (SOMEV (m1, #l)); eauto. }
    iExists _; iFrame; iNext.
    iIntros "Hmb".

    rel_pures_l.
    rel_apply_l (revoke_offer_l with "Htok").
    iIntros (j K') "Hj". iSpecialize ("Hoff" with "Hj").
    iDestruct (offerInv_excl with "HN Hoff") as %?.
    iMod (offerReg_alloc off h2 γ j K' with "HNown") as "[HNown #Hfrag]"; eauto.
    iMod ("Hcl" with "[-]") as "_".
    { iNext. iExists _,_,_; iFrame.
      iSplitL "Hmb".
      - iRight. iExists off, h1, h2, _, _, _. iFrame "Hmb Hh".
        iPureIntro. by rewrite lookup_insert.
      - rewrite /offerInv big_sepM_insert; eauto with iFrame. }
    iModIntro. iNext.
    iInv stackN as (s1' s2' N') "(Hl & Hst1 & Hst2 & Hrel & Hmb & >HNown & HN)" "Hcl".
    iModIntro. iDestruct (offerReg_frag_lookup with "HNown Hfrag") as %Hfoo.
    rewrite /offerInv.
    (* TODO: separate lemma *)
    rewrite (big_sepM_lookup_acc _ N'); eauto.
    iDestruct "HN" as "[$ HN]".
    iNext. iIntros "Hoff". iSplit.
    - (* The offer was already accepted *)
      iSpecialize ("HN" with "Hoff").
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_,_; iFrame. }
      rel_pures_l. rel_values.
    - (* The offer has been successfully revoked. We have to do the actual push. *)
      iSpecialize ("HN" with "Hoff").
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_,_; iFrame. }
      clear.
      rel_pures_l. rel_load_l_atomic.
      iInv stackN as (s1 s2 N) "(>Hl & >Hst1 & >Hst2 & Hrel & Hmb & HNown & HN)" "Hcl"; simplify_eq.
      iModIntro. iExists _. iFrame "Hst1". iNext. iIntros "Hst1".

      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_,_; iFrame. }

      rel_pures_l. rel_alloc_l new as "Hnew". rel_pures_l.

      rel_cmpxchg_l_atomic; first by destruct s1.
      iInv stackN as (s1' s2' N') "(>Hl & >Hst1 & >Hst2 & Hrel & Hmb & HNown & HN)" "Hcl"; simplify_eq.
      iModIntro. iExists _. iFrame "Hst1". iSplit.
      + iIntros (?). iNext. iIntros "Hst1".
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists _,_,_; by iFrame. }
        rel_pures_l. iApply "IH".
      + iIntros (?); simplify_eq/=. iNext.
        iIntros "Hst1".
        rel_apply_r (refines_CG_push_r with "Hst2 Hl").
        iIntros "Hst2 Hl".
        iDestruct (stack_link_cons _ new h1 h2
                     with "Hh Hrel Hnew") as "Hrel".
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists _,_,_; by iFrame. }
        rel_pures_l. rel_values.
  Qed.

  Lemma refinement A :
    ⊢ REL mk_stack #() << CG_mkstack #() : (() → () + A) * (A → ()).
  Proof.
    rel_rec_r. rel_pures_r. rel_rec_r.
    rel_apply_r refines_newlock_r. iIntros (lk) "Hlk".
    rel_pures_r.
    rel_alloc_r st' as "Hst'".
    rel_pure_r. rel_pure_r.  rel_pure_r.  rel_pure_r.  rel_pure_r.
    rel_rec_l. rel_pures_l.
    rel_alloc_l mb as "Hmb". rel_pures_l.
    rel_alloc_l st as "Hst". do 4 rel_pure_l. (*XXX: doing rel_pures_l reduces too much *)
    iMod (own_alloc (● to_offer_reg ∅ : authR offerRegR)) as (γo) "Hor".
    { apply auth_auth_valid. apply to_offer_reg_valid. }
    iMod (inv_alloc stackN _ (stackInv A γo st st' mb lk) with "[-]") as "#Hinv".
    { iNext. unfold stackInv.
      iExists None, _, _. iFrame.
      iSplit; eauto.
      - iApply stack_link_empty.
      - iApply offerInv_empty. }
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
