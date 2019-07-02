(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Fine-grained stack with helping.
Based on the case study <https://iris-project.org/pdfs/2017-case-study-concurrent-stacks-with-helping.pdf> *)
(* It demonstrates how to do _helping_ in Iris. Note that for this
proof we cannot stay inside the ReLoC and we have to unfold some stuff
to get to the actual model of logical relations. The initial version
of this code was written togethe witr Amin Timany around 2017 *)

(* TODO: get rid of the rec_unfold's here *)
From iris.algebra Require Import auth gmap agree list excl.
From iris.base_logic.lib Require Import auth.
From reloc Require Export reloc experimental.helping.mailbox examples.stack.CG_stack lib.list.

Definition pop_st : val := rec: "pop" "r" "get" :=
  match: "get" #() with
    NONE =>
    (match: rec_unfold !"r" with
       NONE => NONE
     | SOME "l" =>
       let: "pair" := !"l" in
       if: CAS "r" (SOME "l") (Snd "pair")
       then SOME (Fst "pair")
       else "pop" "r" "get"
     end)
  | SOME "x" => SOME "x"
  end.

Definition push_st : val := rec: "push" "r" "put" "n" :=
  match: "put" "n" with
    NONE => #()
  | SOME "n" =>
    let: "tail" := !"r" in
    let: "new" := SOME (ref ("n", "tail")) in
    if: CAS "r" "tail" "new"
    then #()
    else "push" "r" "put" "n"
  end.

Definition mk_stack : val :=  λ: "_",
  unpack: "M" := mailbox in
  let: "new_mb" := Fst (Fst "M") in
  let: "put" := Snd (Fst "M") in
  let: "get" := Snd "M" in
  let: "mb" := "new_mb" #() in
  let: "r" := ref NONE in
  (λ: <>, pop_st "r" (λ: <>, "get" "mb"),
   λ: "x", push_st "r" (λ: "n", "put" "mb" "n") "x").

Definition CG_mkstack : val := λ: "_",
  let: "st" := CG_new_stack #() in
  (λ: <>, CG_locked_pop "st", λ: "x", CG_locked_push "st" "x").

(** Algebras needed for the refinement *)
Canonical Structure ectx_itemO := leibnizO ectx_item.

Definition offerReg := gmap loc (val * gname * nat * (list ectx_item)).

Definition offerRegR :=
  gmapUR loc
         (agreeR (prodO valO (prodO gnameO (prodO natO (listO ectx_itemO))))).

Class offerRegPreG Σ := OfferRegPreG {
  offerReg_inG :> authG Σ offerRegR
}.

Section refinement.
  Context `{!relocG Σ,!offerRegPreG Σ, !channelG Σ}.

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

  Definition stackN := nroot .@ "stacked".

  Definition offerInv (N : offerReg) (st' : val) : iProp Σ :=
    ([∗ map] l ↦ w ∈ N,
     match w with
     | (v,γ,j,K) => ∃ (c : nat),
       l ↦ #c ∗
        (⌜c = 0⌝ ∗ j ⤇ fill K (CG_locked_push st' (of_val v))%E
       ∨ ⌜c = 1⌝ ∗ (j ⤇ fill K #() ∨ own γ (Excl ()))
       ∨ ⌜c = 2⌝ ∗ own γ (Excl ()))%nat
     end)%I.

  Lemma offerInv_empty (st' : val) :
    offerInv ∅ st'.
  Proof. by rewrite /offerInv big_sepM_empty. Qed.

  Lemma offerInv_excl (N : offerReg) (st' : val) (o : loc) (v : val) :
    offerInv N st' -∗ o ↦ v -∗ ⌜N !! o = None⌝.
  Proof.
    rewrite /offerInv.
    iIntros "HN Ho".
    iAssert (⌜is_Some (N !! o)⌝ → False)%I as %Hbaz.
    {
      iIntros ([[[[? ?] ?] ?] HNo]).
      rewrite (big_sepM_lookup _ N o _ HNo).
      iDestruct "HN" as (c) "[HNo ?]".
      iDestruct (gen_heap.mapsto_valid_2 with "Ho HNo") as %Hfoo.
      compute in Hfoo. contradiction.
    }
    iPureIntro.
    destruct (N !! o); eauto. exfalso. apply Hbaz; eauto.
  Qed.

  Lemma offerReg_alloc (o : loc) (v : val) (γ : gname)
    (j : nat) (K : list ectx_item) (γo : gname) (N : offerReg)  :
    N !! o = None →
    own γo (● to_offer_reg N)
    ==∗ own γo (● to_offer_reg (<[o:=(v, γ, j, K)]> N))
      ∗ own γo (◯ {[o := to_agree (v, (γ, (j, K)))]}).
  Proof.
    iIntros (HNo) "HN".
    iMod (own_update with "HN") as "[HN Hfrag]".
    { eapply auth_update_alloc.
      eapply (alloc_singleton_local_update _ o (to_agree (v, (γ, (j, K))))); try done.
      by rewrite /to_offer_reg lookup_fmap HNo.
    }
    iFrame.
    by rewrite /to_offer_reg fmap_insert.
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
    rewrite singleton_included=> -[av []].
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

  Definition stackRel (v1 v2 : val) : iProp Σ :=
    lrel_list lrel_int v1 v2.
  Instance stackRel_persistent v1 v2 : Persistent (stackRel v1 v2).
  Proof. apply _. Qed.
  Lemma stackRel_empty : stackRel (InjLV #()) (InjLV #()).
  Proof. apply lrel_list_nil. Qed.
  Hint Resolve stackRel_empty.
  Lemma stackRel_cons (n : Z) t1 t2 :
    ▷ stackRel t1 t2 -∗ stackRel (InjRV (#n, t1)) (InjRV (#n, t2)).
  Proof.
    iIntros "#Hs".
    iApply (lrel_list_cons with "[] Hs").
    iNext. iExists _. iSplit; eauto.
  Qed.
  Lemma stackRel_unfold v1 v2 :
    stackRel v1 v2
         ⊣⊢
    (▷ ((⌜v1 = (InjLV #())⌝ ∧ ⌜v2 = (InjLV #())⌝)
      ∨ ∃ (n : Z) t1 t2, ⌜v1 = (InjRV (#n, t1))⌝
                       ∧ ⌜v2 = (InjRV (#n, t2))⌝
                       ∧ stackRel t1 t2))%I.
  Proof.
    rewrite /stackRel /=.
    rewrite lrel_list_unfold.
    iSplit.
    - iIntros "H". iNext.
      iDestruct "H" as "[H|H]"; first by iLeft.
      iRight. iDestruct "H" as (w1 w2 t1 t2) "(-> & -> & Hw & Ht)".
      iDestruct "Hw" as (n) "[-> ->]".
      iExists n,_,_. eauto with iFrame.
    - iIntros "H". iNext.
      iDestruct "H" as "[H|H]"; first by iLeft.
      iRight. iDestruct "H" as (n t1 t2) "(->&->&Hl)".
      iExists #n,#n,_,_. repeat iSplit; eauto with iFrame.
  Qed.


  Definition oloc_to_val (ol: option loc) : val :=
    match ol with
    | None => NONEV
    | Some loc => SOMEV (#loc)
    end.

  Definition olocO := leibnizO (option loc).

  Local Instance oloc_to_val_inj : Inj (=) (=) oloc_to_val.
  Proof. intros [|][|]; simpl; congruence. Qed.

  Notation D := (olocO -d> valO -d> iProp Σ).

  Definition stack_link_pre : D → D := λ S ol v2,
    match ol return _ with
    | None => ⌜v2 = NONEV⌝
    | Some l => ∃ (h : val) (t : option loc) (h' t' : val),
                  ⌜v2 = SOMEV (h', t')⌝
                ∗ (∃ q, l ↦{q} (h, oloc_to_val t))
                ∗ lrel_int h h' ∗ ▷ S t t'
    end%I.

  Global Instance stack_link_pre_contractive : Contractive stack_link_pre.
  Proof.
    intros n S1 S2 HS. solve_proper_prepare.
    repeat (first [apply HS | f_contractive | f_equiv]).
  Qed.
  Definition stack_link := fixpoint stack_link_pre.

  Lemma stack_link_unfold ol v2 :
    stack_link ol v2 ≡
    (match ol with
     | None => ⌜v2 = NONEV⌝
     | Some l => ∃ (h : val) (t : option loc) (h' t' : val),
                   ⌜v2 = SOMEV (h', t')⌝
                 ∗ (∃ q, l ↦{q} (h, oloc_to_val t))
                 ∗ lrel_int h h' ∗ ▷ stack_link t t'
     end%I).
  Proof. apply (fixpoint_unfold stack_link_pre). Qed.

  Lemma stack_link_empty : stack_link None NILV.
  Proof. rewrite stack_link_unfold; by iPureIntro. Qed.

  Lemma stack_link_cons l h h' t t' q :
    lrel_int h h' -∗
    ▷ stack_link t t' -∗
    l ↦{q} (h, oloc_to_val t) -∗
    stack_link (Some l) (CONSV h' t').
  Proof.
    iIntros "Hh Ht Hl".
    rewrite (stack_link_unfold (Some _)).
    iExists _,_,_,_. iFrame "Hh Ht". iSplit; eauto with iFrame.
  Qed.

  (* Fixpoint is_list xs v : iProp Σ := *)
  (*   (match xs, v with *)
  (*    | [], None => True *)
  (*    | x :: xs, Some l => ∃ t q, l ↦{q} (x, oloc_to_val t)%V ∗ is_list xs t *)
  (*    | _, _ => False *)
  (*    end)%I. *)

  (* Lemma is_list_dup xs v : *)
  (*   is_list xs v -∗ is_list xs v ∗ match v with *)
  (*     | None => True *)
  (*     | Some l => ∃ h t q, l ↦{q} (h, oloc_to_val t)%V *)
  (*     end. *)
  (* Proof. *)
  (*   destruct xs, v; simpl; auto; first by iIntros "[]". *)
  (*   iIntros "H"; iDestruct "H" as (t q) "(Hl & Hstack)". *)
  (*   iDestruct "Hl" as "[Hl1 Hl2]". *)
  (*   iSplitR "Hl2"; first by (iExists _,_; iFrame). by iExists _, _, _. *)
  (* Qed. *)

  (* Lemma is_list_empty xs : *)
  (*   is_list xs None -∗ ⌜xs = []⌝. *)
  (* Proof. *)
  (*   destruct xs; iIntros "Hstack"; auto. *)
  (* Qed. *)

  (* Lemma is_list_cons xs l h t q : *)
  (*   l ↦{q} (h, t)%V -∗ *)
  (*   is_list xs (Some l) -∗ *)
  (*   ∃ ys, ⌜xs = h :: ys⌝. *)
  (* Proof. *)
  (*   destruct xs; first by iIntros "? %". *)
  (*   iIntros "Hl Hstack"; iDestruct "Hstack" as (t' q') "(Hl' & Hrest)". *)
  (*   iDestruct (gen_heap.mapsto_agree with "Hl Hl'") as "%"; simplify_eq; iExists _; auto. *)
  (* Qed. *)

  Definition stackInv oname (st st' mb : loc) (lc : val) : iProp Σ :=
    (∃ ol v2 (N : offerReg), is_locked_r lc false ∗ st ↦ oloc_to_val ol ∗ st' ↦ₛ v2
                                                  ∗ stack_link ol v2
     ∗ (mb ↦ NONEV
        ∨ (∃ (l : loc) (n : Z) γ j K, mb ↦ SOMEV (#n, #l) ∗ ⌜N !! l = Some (#n, γ, j, K)⌝))
     ∗ own oname (● to_offer_reg N)
     ∗ offerInv N (#st', lc))%I.

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

  Lemma pop_no_helping_refinement γo st st' mb lk :
    inv stackN (stackInv γo st st' mb lk) -∗
    □ (REL (pop_st #st) (λ: <>, get_mail #mb)%V
       <<
      CG_locked_pop (#st', lk)%V : () + lrel_int) -∗
    REL match: rec_unfold ! #st with
          InjL <> => InjL #()
        | InjR "l" =>
          let: "pair" := ! "l" in
          if: Snd (CmpXchg #st (InjR "l") (Snd "pair"))
          then InjR (Fst "pair")
          else (pop_st #st) (λ: <>, get_mail #mb)%V
        end
    <<
    CG_locked_pop (#st', lk)%V : () + lrel_int.
  Proof.
    iIntros "#Hinv IH".
    rel_load_l_atomic.
    iInv stackN as (s1 s2 N) "(Hlk & Hst1 & Hst2 & Hrel & >Hmb & HNown & HN)" "Hcl".
    iModIntro. iExists _; iFrame. iNext. iIntros "Hst1".
    rewrite stack_link_unfold.
    destruct s1 as [l|]; last first.
    - (* Stack is empty *)
      iDestruct "Hrel" as "->". iSimpl.
      rel_rec_l. rel_pures_l.
      rel_apply_r (refines_CG_pop_fail_r with "Hst2 Hlk").
      iIntros "Hst' Hlk".
      iMod ("Hcl" with "[-]") as "_".
      { iNext. iExists _,_,_. iFrame.
        iApply stack_link_empty. }
      rel_values. iModIntro. iExists #(),#().
      iLeft; repeat iSplit; eauto with iFrame.
    - iDestruct "Hrel" as (h t h' t' ->) "(Hl & #Hh & Ht)". iSimpl.
      rel_rec_l. rel_pures_l.
      iDestruct "Hl" as "[Hl Hl2]".
      iMod ("Hcl" with "[-IH Hl]") as "_".
      { iNext. iExists _,_,_. iFrame.
        iDestruct "Hl2" as (q) "Hl2".
        iApply (stack_link_cons with "Hh Ht Hl2"). }
      iDestruct "Hl" as (q) "Hl".
      rel_load_l. rel_pures_l.
      rel_cmpxchg_l_atomic.
      iInv stackN as (s1 s2 N') "(Hlk & Hst1 & Hst2 & Hrel & >Hmb & HNown & HN)" "Hcl".
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

  Lemma push_refinement γo st st' mb lk h1 h2 :
    inv stackN (stackInv γo st st' mb lk) -∗
    lrel_int h1 h2 -∗
    REL ((push_st #st) (λ: "n", (put_mail #mb) "n")%V) h1
      <<
    (CG_locked_push (#st', lk)%V) h2 : ().
  Proof.
    iIntros "#Hinv Hh".
    iDestruct "Hh" as (n) "[% %]"; simplify_eq/=.
    iLöb as "IH".
    rel_rec_l.
    rel_pures_l.
    rel_rec_l. rel_pures_l. rel_rec_l.
    rel_alloc_l o as "Ho". rel_pures_l.
    rel_store_l_atomic.
    iInv stackN as (s1 s2 N) "(Hl & Hst1 & Hst2 & Hrel & >Hmb & HNown & HN)" "Hcl".
    iModIntro.
    iAssert (∃ v, ▷ mb ↦ v)%I with "[Hmb]" as (v) "Hmb".
    { iDestruct "Hmb" as "[Hmb | Hmb]".
      - iExists (InjLV #()); eauto.
      - iDestruct "Hmb" as (l m γ j K) "[Hmb ?]".
        iExists (InjRV (#m, #l)); eauto. }
    iExists _; iFrame; iNext.
    iIntros "Hmb".
    rel_pures_l.
    rel_rec_l.
    iDestruct (offerInv_excl with "HN Ho") as %Hbaz.
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    rewrite {2}refines_eq /refines_def.
    iIntros (ρ) "#Hs".
    iIntros (j K) "Hj".
    iMod (offerReg_alloc o #n γ j K with "HNown") as "[HNown Hfrag]"; eauto.
    iMod ("Hcl" with "[-Hfrag Hγ]") as "_".
    { iNext. iExists _,_,_; iFrame.
      iSplitL "Hmb".
      - iRight. iExists o, n, _, _, _. iFrame "Hmb".
        iPureIntro. by rewrite lookup_insert.
      - rewrite /offerInv big_sepM_insert; eauto.
        iFrame.
        iExists 0%nat. iFrame "Ho".
        iLeft. unlock CG_locked_push. iFrame "Hj". eauto. }
    iModIntro. wp_proj.
    wp_bind (CmpXchg _ _ _).
    iInv stackN as (s1' s2' N') "(Hl & Hst1 & Hst2 & Hrel & >Hmb & >HNown & HN)" "Hcl".
    iDestruct (offerReg_frag_lookup with "HNown Hfrag") as %Hfoo.
    rewrite /offerInv.
    rewrite (big_sepM_lookup_acc _ N'); eauto.
    iDestruct "HN" as "[HoN HN]".
    iDestruct "HoN" as (c) ">[Ho Hc]".
    destruct (decide (c = 0%nat)); subst.
    * wp_cmpxchg_suc; first done.
      iDestruct "Hc" as "[[% Hj] | [[% Hc] | [% Hc]]]"; [ | congruence..].
      iMod ("Hcl" with "[-Hj Hfrag]").
      { iNext. iExists _,_,_; iFrame.
        iApply "HN". iExists 2%nat; eauto with iFrame. }
      iModIntro. wp_pures.
      wp_bind (! #st)%E. clear s1 s2 Hbaz N.
      iInv stackN as (s1 s2 N) "(>Hl & >Hst1 & >Hst2 & Hrel & Hmb & HNown & HN)" "Hcl"; simplify_eq.
      wp_load.
      iMod ("Hcl" with "[-Hj Hfrag]") as "_".
      { iNext. iExists _,_,_; by iFrame. }
      iModIntro. wp_pures. wp_alloc hd as "Hhd". wp_pures.
      wp_bind (CmpXchg _ _ _).
      clear s1' s2' N.
      iInv stackN as (s1' s2' N) "(>Hl & >Hst1 & >Hst2 & Hrel & Hmb & HNown & HN)" "Hcl"; simplify_eq.
      destruct (decide (s1 = s1')) as [->|?].
      ** (** CAS/push succeeds *)
        wp_cmpxchg_suc. destruct s1'; left; done.
        unlock {2}CG_locked_push.
        (* TODO: This is horrible *)
        tp_pure j (App _ (_,_)%V). iSimpl in "Hj".
        tp_pure j (Rec _ _ _). iSimpl in "Hj".
        repeat (tp_pure j _; iSimpl in "Hj").
        tp_pure j (Snd _). iSimpl in "Hj".
        unlock acquire. tp_pure j (App _ lk). iSimpl in "Hj".
        unlock is_locked_r. iDestruct "Hl" as (lk' ->) "Hl".
        tp_cmpxchg_suc j. iSimpl in "Hj".
        tp_pure j (Snd _). iSimpl in "Hj".
        tp_if j. iSimpl in "Hj".
        tp_pure j (Rec _ _ _). iSimpl in "Hj".
        tp_rec j. iSimpl in "Hj".

        unlock CG_push.
        tp_pure j (Fst _). iSimpl in "Hj".
        tp_pure j (App _ #st'). iSimpl in "Hj".
        tp_pure j (Rec _ _ _). iSimpl in "Hj".
        tp_pure j (App _ #n). iSimpl in "Hj".
        tp_load j. iSimpl in "Hj".
        tp_pure j (Pair _ _).
        tp_pure j (InjR _).
        tp_store j. iSimpl in "Hj".
        tp_pure j (Rec _ _ _).
        tp_rec j. iSimpl in "Hj".
        tp_pure j (Snd _). unlock release.
        tp_rec j. tp_store j.
        iDestruct (stack_link_cons hd #n #n
                     with "[] Hrel Hhd") as "Hrel".
        { iExists n. eauto with iFrame. }
        iMod ("Hcl" with "[-Hj]").
        { iNext. iExists _,_,_; subst; iFrame.
          iExists _; by iFrame "Hl". }
        iModIntro. wp_pures.
        iExists #(); iFrame; eauto.
      ** (** CAS FAILS  *)
        wp_cmpxchg_fail.
        { destruct s1', s1; simplify_eq/=; eauto.
          congruence. }
        { destruct s1', s1; simplify_eq/=; eauto. }
        iMod ("Hcl" with "[-Hj]") as "_".
        { iNext. iExists _,_,_; subst; eauto with iFrame. }
        iModIntro. wp_pure _. wp_if.
        rewrite refines_eq /refines_def.
        iApply fupd_wp.
        iApply ("IH" with "Hs Hj").
    * iDestruct "Hc" as "[[% Hc] | [[% Hj] | [% Hc]]]"; [congruence | |]; last first.
      iDestruct (own_valid_2 with "Hγ Hc") as %Hbar.
      inversion Hbar.
      iDestruct "Hj" as "[Hj | Hc]"; last first.
      iDestruct (own_valid_2 with "Hγ Hc") as %Hbar.
      inversion Hbar.
      wp_cmpxchg_fail.
      { simplify_eq/=; eauto. }
      iMod ("Hcl" with "[-Hj]") as "_".
      { iNext. iExists _,_,_; iFrame.
        iApply "HN".
        simpl. iExists _. iFrame.
        iRight. iLeft. iSplit; eauto. }
      iModIntro. wp_pures.
      iExists #(); eauto.
  Qed.

  Lemma refinement :
    REL mk_stack #() << CG_mkstack #() :
      (() → () + lrel_int) * (lrel_int → ()).
  Proof.
    rel_rec_r. rel_pures_r. rel_rec_r.
    rel_apply_r refines_newlock_r. iIntros (lk) "Hlk".
    rel_pures_r.
    rel_alloc_r st' as "Hst'".
    rel_pure_r. rel_pure_r.  rel_pure_r.  rel_pure_r.  rel_pure_r.
    rel_rec_l. rel_pures_l. rel_rec_l. rel_pures_l.
    rel_rec_l. rel_pures_l.
    rel_alloc_l mb as "Hmb". rel_pures_l.
    rel_alloc_l st as "Hst". rel_pure_l. rel_pure_l. rel_pure_l. rel_pure_l.
    iMod (own_alloc (● to_offer_reg ∅ : authR offerRegR)) as (γo) "Hor".
    { apply auth_auth_valid. apply to_offer_reg_valid. }
    iMod (inv_alloc stackN _ (stackInv γo st st' mb lk) with "[-]") as "#Hinv".
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
      iLöb as "IH".
      rel_rec_l. rel_pures_l.
      rel_rec_l.
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
        iDestruct "Hmb" as (l v γ j K) "[Hmb >HNl]".
        iDestruct "HNl" as %HNl.
        rewrite /offerInv big_sepM_lookup_acc; eauto.
        iDestruct "HN" as "[HNl HN]".
        simpl. iMod "HNown".
        iMod (offerReg_lookup_frag with "HNown") as "[#Hlown HNown]"; eauto.
        iModIntro. iExists _; iFrame.
        iNext. iIntros "Hmb".
        iMod ("Hcl" with "[-Hlown IH]") as "_".
        { iNext. iExists _, _, _; iFrame.
          iSplitL "Hmb".
          iRight. iExists _, _. iFrame.
          iPureIntro. do 3 eexists; eauto.
          by iApply "HN". }
        rel_pures_l. rel_rec_l. rel_pures_l.
        (* Trying to take upon the offer *)
        rel_cmpxchg_l_atomic.
        iInv stackN as (s1' s2' N') "(>Hl & >Hst1 & >Hst2 & Hrel & Hmb & HNown & HN)" "Hcl"; simplify_eq.
        iMod "HNown".
        iDestruct (offerReg_frag_lookup with "HNown Hlown") as %?.
        rewrite /offerInv (big_sepM_lookup_acc _ _ l); eauto.
        iDestruct "HN" as "[HNl HN]".
        iDestruct "HNl" as (c) "[>HNl Hc]".
        iModIntro. iExists _; iFrame.
        iSplit; last first.
        + (* CAS suc *)
          iIntros (Hc); simplify_eq/=. iNext.
          assert (c = 0%nat) as -> by lia. (* :) *)
          iIntros "HNl".
          rel_pures_l.
          iDestruct "Hc" as "[[% Hj] | [[% ?] | [% ?]]]"; [| congruence..].
          unlock {1}CG_locked_push.
          unlock {1}acquire {1}release.
          (* THIS IS COPY PASTED :-) *)
          tp_pure j (App _ (_,_)%V). iSimpl in "Hj".
          tp_pure j (Rec _ _ _). iSimpl in "Hj".
          repeat (tp_pure j _; iSimpl in "Hj").
          tp_pure j (Snd _). iSimpl in "Hj".
          unlock acquire. tp_pure j (App _ lk). iSimpl in "Hj".
          unlock is_locked_r. iDestruct "Hl" as (lk' ->) "Hl".
          (* TODO: make all the tp_ tactics work without the need for an explicit Fupd *)
          iApply refines_spec_ctx.
          iDestruct 1 as (ρ) "#Hρ".
          iApply fupd_refines.
          (* because we manually applied `fupd_refines`, the tactical `with_spec_ctx` doesn't work anymore *)
          tp_cmpxchg_suc j. iSimpl in "Hj".
          tp_pure j (Snd _). iSimpl in "Hj".
          tp_if j. iSimpl in "Hj".
          tp_pure j (Rec _ _ _). iSimpl in "Hj".
          tp_rec j. iSimpl in "Hj".

          unlock CG_push.
          tp_pure j (Fst _). iSimpl in "Hj".
          tp_pure j (App _ #st'). iSimpl in "Hj".
          tp_pure j (Rec _ _ _). iSimpl in "Hj".
          tp_pure j (App _ #v). iSimpl in "Hj".
          tp_load j. iSimpl in "Hj".
          tp_pure j (Pair _ _).
          tp_pure j (InjR _).
          tp_store j. iSimpl in "Hj".
          tp_pure j (Rec _ _ _).
          tp_rec j. iSimpl in "Hj".
          tp_pure j (Snd _). unlock release.
          tp_rec j. tp_store j.
          iClear "Hρ". clear ρ. iModIntro.

          rel_apply_r (refines_CG_pop_suc_r with "Hst2 [Hl]").
          { iExists _. by iFrame "Hl". }
          iIntros "Hst2 Hl".
          iMod ("Hcl" with "[-]") as "_".
          { iNext. iExists _,_,_. iFrame.
            iApply "HN".
            iExists 1%nat. iFrame "HNl".
            iRight. iLeft. eauto with iFrame. }
          rel_values. iModIntro. iExists #v,#v.
          iRight. repeat iSplit; eauto with iFrame.
        + (* CAS FAILS *)
          iIntros (Hc). iNext.
          iIntros "HNl".
          iMod ("Hcl" with "[-IH]") as "_".
          { iNext. iExists _,_,_. iFrame.
            iApply "HN". iExists _. iFrame. }
          rel_pures_l.
          iApply (pop_no_helping_refinement with "Hinv IH"). }
  Qed.


End refinement.
