(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Generic operations for helping.
    The operation mk_helping : (() → ( () → option A ) × ( A → () )) → ( () → option A ) × ( A → () )
    takes a "constructor" that returns two closures, and returns two /wrapped/ closures.
    The wrapped closures (for "pop" and "push" operations) synchronize on a side channel.

    This provides a somewhat generic proof of the refinement for stack with helping.

    TODO: support recursion/callbacks into the wrapped functions.
 *)
From iris.algebra Require Import auth gmap agree list excl.
From reloc Require Export reloc examples.stack_helping.offers.
From reloc Require Import lib.list.

(* wrapper for pop *)
Definition wrap_pop : val := λ: "f" "mb",
  match: !"mb" with
    NONE =>
    (* there are no offers *) "f" #()
  | SOME "off" =>
    (* trying to accept an offer instead of doing an actual POP *)
    match: take_offer "off" with
      NONE => (* did not succeed on accepting the offer *)
      "f" #()
    | SOME "x" => SOME "x"
    end
  end.

(* wrapper for push *)
Definition wrap_push : val := λ: "f" "mb" "x",
  let: "off" := mk_offer "x" in
  "mb" <- SOME "off";;
  match: revoke_offer "off" with
    NONE => (* the offer was successfully taken *) #()
  | SOME "x" =>
    (* nobody took the offer  *)
    "f" "x" (* TODO: add a way of restartnig "f" using mk_helping_2 *)
  end.

Definition mk_helping : val := λ: "new_ds",
  let: "ff" := "new_ds" #() in
  let: "f1" := Fst "ff" in
  let: "f2" := Snd "ff" in
  let: "mb" := ref NONE in
  (λ: <>, wrap_pop "f1" "mb",
   λ: "x", wrap_push "f2" "mb" "x").

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
  offerReg_inG :: inG Σ (authUR offerRegR)
}.

Definition offerize (x : (val * gname * ref_id)) :
  (agreeR (prodO valO (prodO gnameO ref_idO))) :=
  match x with
  | (v, γ, k) => to_agree (v, (γ, k))
  end.

Definition to_offer_reg : offerReg -> offerRegR := fmap offerize.

Lemma to_offer_reg_valid N : ✓ to_offer_reg N.
Proof.
  intros l. rewrite lookup_fmap. case: (N !! l); simpl; try done.
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
    iCombine "HN Hfrag" gives %Hfoo.
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
        destruct ((offerize <$> N !! i)) as [?|] eqn:He;
          rewrite He; simpl; done. }
    by rewrite Hfoo.
  Qed.

  (** The invariant that we will have. *)
  Definition offerInv `{!relocG Σ} (N : offerReg) (f : val) : iProp Σ :=
    ([∗ map] l ↦ w ∈ N,
     match w with
     | (v,γ,k) => is_offer γ l
                             (refines_right k (f (of_val v))%E)
                             (refines_right k #())
     end)%I.

  Lemma offerInv_empty `{!relocG Σ} (f : val) : ⊢ offerInv ∅ f.
  Proof. by rewrite /offerInv big_sepM_empty. Qed.

  Lemma offerInv_excl `{!relocG Σ} (N : offerReg) (f : val) (o : loc) γ P Q :
    offerInv N f -∗ is_offer γ o P Q -∗ ⌜N !! o = None⌝.
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


(** * Refinement proof *)
Section refinement.
  Context `{!relocG Σ, !offerRegPreG Σ, !offerG Σ}.

  Implicit Type A : lrel Σ.

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


  (* ************************************************** *)
  (** ** The main invariant that we will use for the proof *)
  Definition iN := nroot.@"hewwo".
  Definition I A oname (mb : loc) (push_f : val) : iProp Σ :=
    (∃ (N : offerReg),
        (mb ↦ NONEV      (* the mailbox is either empty or contains an offer that is in the registry *)
        ∨ (∃ (l : loc) v1 v2 γ k,
              A v1 v2
            ∗ mb ↦ SOMEV (v1, #l)
            ∗ ⌜N !! l = Some (v2, γ, k)⌝))
     ∗ own oname (● to_offer_reg N)
     ∗ offerInv N push_f)%I.

  Lemma wrap_pop_refinement A (pop1 pop2 push2 : val) γo mb :
    inv iN (I A γo mb push2) -∗
    (∀ e v2 k, refines_right k (push2 (of_val v2)) -∗
                   (refines_right k #() -∗ REL e << SOMEV v2 @ ⊤∖↑iN : () + A) -∗
                   REL e << pop2 #() @ ⊤∖↑iN : () + A) -∗
    (REL pop1 << pop2 : () → () + A) -∗
    REL wrap_pop pop1 #mb
      <<
    pop2 #() : () + A.
  Proof.
    iIntros "#Hinv HpopGhost Hpop".
    iLöb as "IH".
    rel_rec_l. rel_pures_l.
    rel_load_l_atomic.
    iInv iN as (N) "(Hmb & HNown & HN)" "Hcl".
    iDestruct "Hmb" as "[Hmb | Hmb]".
    - (* NO OFFER *)
      iModIntro. iExists _; iFrame.
      iNext. iIntros "Hmb".
      rel_pures_l.
      iMod ("Hcl" with "[-Hpop HpopGhost]") as "_".
      { iNext. iExists N; by iFrame. }
      iApply (refines_app with "Hpop"). by rel_values.
    - (* YES OFFER *)
      iDestruct "Hmb" as (l v1 v2 γ k) "(#Hv & Hmb & >HNl)".
      iDestruct "HNl" as %HNl.
      rewrite /offerInv big_sepM_lookup_acc; eauto. iSimpl in "HN".
      iDestruct "HN" as "[HNl HN]".
      iMod "HNown".
      iMod (offerReg_lookup_frag with "HNown") as "[#Hlown HNown]"; eauto.
      iModIntro. iExists _; iFrame.
      iNext. iIntros "Hmb".
      iMod ("Hcl" with "[-Hlown IH Hpop HpopGhost]") as "_".
      { iNext. iExists _. iFrame.
        iSplitL "Hmb".
        - iRight. iExists _, _, _, _, _.
          eauto with iFrame.
        - by iApply "HN". }

      rel_pures_l. rel_apply_l (take_offer_l _ ).
      iInv iN as (N') "(Hmb & HNown & HN)" "Hcl".
      simplify_eq/=.
      iMod "HNown".
      iDestruct (offerReg_frag_lookup with "HNown Hlown") as %?.
      rewrite /offerInv (big_sepM_lookup_acc _ _ l); eauto. iSimpl in "HN".
      iDestruct "HN" as "[HNl HN]". iModIntro.
      iFrame "HNl". iNext. iSplit.
      +  (* Did not manage to accept an offer *)
        iIntros "HNl".
        iMod ("Hcl" with "[-IH Hpop]") as "_".
        { iNext. iExists _. iFrame.
          by iApply "HN". }
        rel_pures_l.
        iApply (refines_app with "Hpop"). by rel_values.
      + (* An offer was accepted *)
        iIntros "Hj Hoff". rel_pures_l.
        iApply ("HpopGhost" with "Hj").
        iIntros "Hj".
        iSpecialize ("Hoff" with "Hj").
        iSpecialize ("HN" with "Hoff").
        iMod ("Hcl" with "[-]") as "_".
        { iNext. iExists _. by eauto with iFrame. }
        rel_values. iModIntro. iExists v1,v2.
        iRight. repeat iSplit; eauto with iFrame.
  Qed.

  Lemma wrap_push_refinement A (push1 push2 : val) γo mb (h1 h2 : val) :
    inv iN (I A γo mb push2) -∗
    A h1 h2 -∗
    (REL push1 << push2 : A → ()) -∗
    REL wrap_push push1 #mb h1
      <<
    push2 h2 : ().
  Proof.
    iIntros "#Hinv #Hh Hpush".
    iLöb as "IH".
    rel_rec_l.
    rel_pures_l.
    rel_apply_l mk_offer_l. iIntros (γ off) "Hoff Htok".
    rel_pures_l.
    rel_store_l_atomic. (* we update the mailbox and store the offer in the registry *)
    iInv iN as (N) "(Hmb & HNown & HN)" "Hcl".
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
    iIntros (j) "Hj". iSpecialize ("Hoff" with "Hj").
    iDestruct (offerInv_excl with "HN Hoff") as %?.
    iMod (offerReg_alloc off h2 γ with "HNown") as "[HNown #Hfrag]"; eauto.
    iMod ("Hcl" with "[-Hpush]") as "_".
    { iNext. iExists _. iFrame "HNown".
      iSplitL "Hmb".
      - iRight. iExists off, h1, h2, _, _. iFrame "Hmb Hh".
        iPureIntro. by rewrite lookup_insert.
      - rewrite /offerInv big_sepM_insert; eauto with iFrame. }
    iModIntro. iNext.
    iInv iN as (N') "(Hmb & HNown & HN)" "Hcl".
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
      iMod ("Hcl" with "[-Hpush]") as "_".
      { iNext. iExists _; iFrame. }
      rel_pures_l. rel_values.
    - (* The offer has been successfully revoked. We have to do the actual push. *)
      iSpecialize ("HN" with "Hoff").
      iMod ("Hcl" with "[-Hpush]") as "_".
      { iNext. iExists _; iFrame. }
      clear.
      rel_pures_l. iApply (refines_app with "Hpush").
      by rel_values.
  Qed.

End refinement.

From reloc.examples.stack Require Import CG_stack refinement.
Definition stackN := nroot.@"stackhehehe".

Section stack_example.
  Context `{!relocG Σ, !offerRegPreG Σ, !offerG Σ, !lockG Σ}.

  Definition stackI stl lk :=
    (∃ γ, is_lock (nroot.@"LoCk") γ lk (∃ ls1, stl ↦{#1/2} val_of_list ls1))%I.
  Definition stackInv A st st' :=
    (∃ (stl : loc) lk, ⌜st = (#stl, lk)%V⌝ ∗
       stackI stl lk ∗
       inv stackN (∃ ls1 ls2,
                      (stl ↦{#1/2} val_of_list ls1)
                    ∗ is_stack st' ls2
                    ∗ ([∗ list] v1;v2 ∈ ls1;ls2, A v1 v2)))%I.

  Lemma pop_refinement A mb γo st (st' : val) :
    inv iN (I A γo mb (λ: "x", CG_locked_push st' "x")) -∗
    stackInv A st st' -∗
    REL wrap_pop (λ: <>, CG_locked_pop st)%V #mb
      <<
     (λ: <>, CG_locked_pop st')%V #() : () + A.
  Proof.
    iIntros "#Hinv #Hstack".
    iApply (wrap_pop_refinement with "Hinv [] []").
    { iIntros (e v2 j) "Hj Hcont".
      rel_pures_r.
      iDestruct "Hstack" as (st1l lk1 ->) "[#HstI #Hstack]".
      iInv stackN as (ls1 ls2) "(Hst1 & >Hst2 & HA)" "Hcl".
      iDestruct "Hst2" as (st2l lk2 ->) "[Hlk Hst2]".
      tp_rec j. tp_pures j. tp_rec j. tp_pures j. tp_rec j.
      unlock is_locked_r. iDestruct "Hlk" as (lk' ->) "Hl".
      tp_cmpxchg_suc j.
      tp_pures j. tp_rec j. tp_pures j.
      tp_load j. tp_pures j.
      tp_store j. tp_pures j.
      tp_rec j. tp_store j.
      rel_apply_r (refines_CG_pop_suc_r with "[Hst2 Hl]").
      { iExists st2l,#lk'. rewrite /is_locked_r. by eauto with iFrame. }
      iIntros "Hst2".
      iMod ("Hcl" with "[-Hcont Hj]") as "_".
      { iNext. iExists _,_. by eauto with iFrame. }
      by iApply "Hcont". }
  { rel_arrow_val. iIntros (??) "[-> ->]". rel_pures_l. rel_pures_r.
    iDestruct "Hstack" as (st1l lk1 ->) "[#HstI #Hstack]". rewrite /stackI.
    iDestruct "HstI" as (γlk) "HstI".
    rel_rec_l. rel_pures_l. rel_apply_l (refines_acquire_l with "HstI").
    iNext. iIntros "Hlocked". iDestruct 1 as (ls1) "Hl1".
    rel_pures_l. rel_rec_l. rel_load_l.
    destruct ls1 as [|h1 ls1]; simpl; rel_rec_l; rel_pures_l.
    - iInv stackN as (ls1 ls2) "(>Hst1 & >Hst2 & HA)" "Hcl".
      iDestruct "Hst2" as (st2l lk2 ->) "[Hlk Hst2]".
      iDestruct (pointsto_agree with "Hl1 Hst1") as %Hfoo.
      assert (ls1 = []) as ->.
      { revert Hfoo; by destruct ls1. }
      rel_rec_r. rel_pures_r. rel_apply_r (refines_acquire_r with "Hlk").
      iIntros "Hlk". rel_pures_r. rel_rec_r. rel_load_r.
      rewrite big_sepL2_later_1. iMod "HA" as "HA".
      rewrite big_sepL2_nil_inv_l. iDestruct "HA" as "->".
      rel_rec_r. rel_pures_r.
      rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
      iMod ("Hcl" with "[-Hl1 Hlocked]") as "_".
      { iNext. iExists [], []. simpl. iFrame.
        rewrite right_id. iExists _,_. eauto with iFrame. }
      rel_apply_l (refines_release_l with "HstI Hlocked [Hl1]").
      { iExists []. eauto with iFrame. }
      iNext. rel_pures_l; rel_pures_r; rel_values.
      iModIntro. iExists _,_. eauto with iFrame.
    - rel_store_l_atomic.
      iInv stackN as (ls1' ls2) "(>Hst1 & >Hst2 & HA)" "Hcl".
      iDestruct "Hst2" as (st2l lk2 ->) "[Hlk Hst2]".
      iDestruct (pointsto_agree with "Hl1 Hst1") as %Hfoo.
      assert (ls1' = h1::ls1) as ->.
      { destruct ls1'; simplify_eq/=; eauto. }
      iModIntro. iExists _. iFrame. iNext. iIntros "Hl1".
      rewrite big_sepL2_cons_inv_l. iDestruct "HA" as (h2 l2' ->) "[#Hh HA]".
      rel_rec_r. rel_pures_r. rel_apply_r (refines_acquire_r with "Hlk").
      iIntros "Hlk". rel_pures_r. rel_rec_r. rel_load_r.
      rel_rec_r. rel_pures_r. rel_store_r. rel_pures_r.
      rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
      iDestruct "Hl1" as "[Hl1 Hst1]".
      iMod ("Hcl" with "[-Hl1 Hlocked]") as "_".
      { iNext. iExists _,_. simpl. iFrame.
        iExists _,_. eauto with iFrame. }
      rel_pures_l.
      rel_apply_l (refines_release_l with "HstI Hlocked [Hl1]").
      { iExists _. eauto with iFrame. }
      iNext. rel_pures_l; rel_pures_r; rel_values.
      iModIntro. iExists _,_. eauto with iFrame. }
  Qed.

  Lemma push_refinement A mb γo st (st' : val) (h1 h2 : val) :
    inv iN (I A γo mb (λ: "x", CG_locked_push st' "x")) -∗
    stackInv A st st' -∗
    A h1 h2 -∗
    REL wrap_push (λ: "x", CG_locked_push st "x")%V #mb h1
      <<
     (λ: "x", CG_locked_push st' "x")%V h2 : ().
  Proof.
    iIntros "#Hinv #Hstack Hh".
    iApply (wrap_push_refinement with "Hinv Hh []").
    rel_arrow_val.
    iIntros (v1 v2) "#Hv". rel_pures_l; rel_pures_r.
    iDestruct "Hstack" as (st1l lk1 ->) "[#HstI #Hstack]". rewrite /stackI.
    iDestruct "HstI" as (γlk) "HstI".
    rel_rec_l. rel_pures_l. rel_apply_l (refines_acquire_l with "HstI").
    iNext. iIntros "Hlocked". iDestruct 1 as (ls1) "Hl1".
    rel_pures_l. rel_rec_l. rel_load_l. rel_pures_l.
    rel_store_l_atomic.
    iInv stackN as (ls1' ls2) "(>Hst1 & >Hst2 & HA)" "Hcl".
    iDestruct "Hst2" as (st2l lk2 ->) "[Hlk Hst2]".
    iDestruct (pointsto_agree with "Hl1 Hst1") as %Hfoo. simplify_eq/=.
    iModIntro. iExists _. iFrame. iNext. iIntros "Hl1".
    rel_rec_r. rel_pures_r. rel_apply_r (refines_acquire_r with "Hlk").
    iIntros "Hlk". rel_pures_r. rel_rec_r. rel_load_r.
    rel_pures_r. rel_store_r. rel_pures_r.
    rel_apply_r (refines_release_r with "Hlk"). iIntros "Hlk".
    iDestruct "Hl1" as "[Hl1 Hst1]".
    iMod ("Hcl" with "[-Hl1 Hlocked]") as "_".
    { iNext. iExists (v1::ls1'),(v2::ls2). simpl. iFrame "Hst1 HA Hv".
      iExists _,_. eauto with iFrame. }
    rel_pures_l.
    rel_apply_l (refines_release_l with "HstI Hlocked [Hl1]").
    { iExists (_::_). eauto with iFrame. }
    iNext. rel_pures_l; rel_pures_r; rel_values.
  Qed.

  Definition CG_mkstack : val := λ: <>,
    let: "st" := CG_new_stack #() in
    (λ: <>, CG_locked_pop "st", λ: "x", CG_locked_push "st" "x").

  Lemma stack_refinement :
    ⊢ REL (Λ: mk_helping CG_mkstack)%V << CG_mkstack : ∀ A, (() → () + A) * (A → ()).
  Proof.
    rel_values. iModIntro. iIntros (A). iModIntro.
    iIntros (? ?) "[-> ->]".
    rel_rec_r. rel_pures_r. rel_rec_r. rel_pures_r.
    rel_alloc_r st' as "Hst2". rel_pures_r.
    rel_apply_r refines_newlock_r. iIntros (lk2) "Hlk2".
    do 5 rel_pure_r.
    rel_rec_l. rel_rec_l. rel_rec_l. rel_rec_l.
    rel_alloc_l st as "[Hst1 Hl1]". rel_pures_l.
    rel_apply_l (refines_newlock_l (nroot.@"LoCk") (∃ ls1, st ↦{#1/2} val_of_list ls1)%I with "[Hl1]").
    { iExists []. iFrame. }
    iNext. iIntros (lk1 γ) "#Hlk1". rel_pures_l.
    rel_alloc_l mb as "Hmb".
    do 4 rel_pure_l.

    iMod (own_alloc (● to_offer_reg ∅ : authR offerRegR)) as (γo) "Hor".
    { apply auth_auth_valid. apply to_offer_reg_valid. }
    iMod (inv_alloc stackN _ (∃ ls1 ls2,
                      (st ↦{#1/2} val_of_list ls1)
                    ∗ is_stack (#st',lk2) ls2
                    ∗ ([∗ list] v1;v2 ∈ ls1;ls2, A v1 v2)) with "[Hst1 Hst2 Hlk2]") as "#Hinv".
    { iNext. iExists [], []; simpl; iFrame. rewrite right_id.
      iExists _,_. eauto with iFrame. }
    iMod (inv_alloc iN _ (I A γo mb _) with "[-Hlk1]") as "#Hofferinv".
    { iNext. iExists ∅. iFrame. iApply offerInv_empty. }
    iApply refines_pair.
    - rel_arrow_val. iIntros (? ?) "[% %]"; simplify_eq/=.
      rel_pure_l.
      iApply (pop_refinement with "Hofferinv").
      iExists _, _. rewrite /stackI.
      eauto with iFrame.
    - rel_arrow_val. iIntros (h1 h2) "#Hh"; simplify_eq/=.
      rel_pures_l.
      iApply (push_refinement with "Hofferinv [-] Hh").
      iExists _, _. rewrite /stackI.
      eauto with iFrame.
  Qed.

End stack_example.
