(* ReLoC -- Relational logic for fine-grained concurrency *)
(** A resource algebra for the specification programs. *)
From iris.algebra Require Import auth excl gmap agree list frac.
From iris.bi Require Export fractional.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang primitive_laws.
Import uPred.

Definition relocN := nroot .@ "reloc".
Definition specN := relocN .@ "spec".

(** The CMRA for the heap of the specification. *)
Definition heapUR (L V : Type) `{Countable L} : ucmra :=
  gmapUR L (prodR fracR (agreeR (leibnizO V))).
Definition tpoolUR : ucmra := gmapUR nat (exclR exprO).
Definition cfgUR := prodUR tpoolUR (heapUR loc (option val)).

(** The CMRA for the thread pool. *)
Class cfgSG Σ := CFGSG { cfg_inG :: inG Σ (authR cfgUR); cfg_name : gname }.
Class relocG Σ := RelocG {
  relocG_heapG :: heapGS Σ;
  relocG_cfgG :: cfgSG Σ;
}.

Definition to_heap {L V} `{Countable L} : gmap L V → heapUR L V :=
  fmap (λ v, (1%Qp, to_agree (v : leibnizO V))).
Definition to_tpool (tp : list expr) : tpoolUR := Excl <$> (map_seq 0 tp).

Section definitionsS.
  Context `{cfgSG Σ, invGS Σ}.

  Definition heapS_pointsto_def (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own cfg_name (◯ (∅, {[ l := (q, to_agree (Some v)) ]})).
  Definition heapS_pointsto_aux : seal (@heapS_pointsto_def). by eexists. Qed.
  Definition heapS_pointsto := heapS_pointsto_aux.(unseal).
  Definition heapS_pointsto_eq :
    @heapS_pointsto = @heapS_pointsto_def := heapS_pointsto_aux.(seal_eq).

  Definition tpool_pointsto_def (j : nat) (e: expr) : iProp Σ :=
    own cfg_name (◯ ({[ j := Excl e ]}, ∅)).
  Definition tpool_pointsto_aux : seal (@tpool_pointsto_def). by eexists. Qed.
  Definition tpool_pointsto := tpool_pointsto_aux.(unseal).
  Definition tpool_pointsto_eq :
    @tpool_pointsto = @tpool_pointsto_def := tpool_pointsto_aux.(seal_eq).

  Definition mkstate (σ : gmap loc (option val)) (κs : gset proph_id) :=
    {| heap := σ; used_proph_id := κs |}.
  Definition spec_inv ρ : iProp Σ :=
    (∃ tp σ, own cfg_name (● (to_tpool tp, to_heap (heap σ)))
                 ∗ ⌜rtc erased_step ρ (tp,σ)⌝)%I.
  Definition spec_ctx : iProp Σ :=
    (∃ ρ, inv specN (spec_inv ρ))%I.

  Global Instance heapS_pointsto_timeless l q v : Timeless (heapS_pointsto l q v).
  Proof. rewrite heapS_pointsto_eq. apply _. Qed.
  Global Instance tpool_pointsto_timeless j e: Timeless (tpool_pointsto j e).
  Proof. rewrite tpool_pointsto_eq. apply _. Qed.
  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.
End definitionsS.

Notation "l ↦ₛ{ q } v" := (heapS_pointsto l q v)
  (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope.
Notation "l ↦ₛ v" := (heapS_pointsto l 1 v) (at level 20) : bi_scope.
Notation "j ⤇ e" := (tpool_pointsto j e) (at level 20) : bi_scope.

Section conversions.
  Context `{cfgSG Σ}.

  Local Open Scope nat_scope.
  (** Conversion to tpools and back *)
  Lemma to_tpool_valid es : ✓ to_tpool es.
  Proof.
    rewrite /to_tpool. move: 0.
    induction es as [|e es]=> n /= //.
    rewrite fmap_insert. by apply insert_valid.
  Qed.

  Lemma tpool_lookup tp j : to_tpool tp !! j = Excl <$> tp !! j.
  Proof.
    unfold to_tpool. rewrite lookup_fmap.
    by rewrite lookup_map_seq_0.
  Qed.
  Lemma tpool_lookup_Some tp j e : to_tpool tp !! j = Excl' e → tp !! j = Some e.
  Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.
  Hint Resolve tpool_lookup_Some : core.

  Lemma to_tpool_insert tp j e :
    j < length tp →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    intros. apply: map_eq=> i. destruct (decide (i = j)) as [->|].
    - by rewrite tpool_lookup lookup_insert list_lookup_insert.
    - rewrite tpool_lookup lookup_insert_ne // list_lookup_insert_ne //.
      by rewrite tpool_lookup.
  Qed.
  Lemma to_tpool_insert' tp j e :
    is_Some (to_tpool tp !! j) →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    rewrite tpool_lookup fmap_is_Some lookup_lt_is_Some. apply to_tpool_insert.
  Qed.
  Lemma to_tpool_snoc tp e :
    to_tpool (tp ++ [e]) = <[length tp:=Excl e]>(to_tpool tp).
  Proof.
    intros. apply: map_eq=> i.
    destruct (lt_eq_lt_dec i (length tp)) as [[?| ->]|?].
    - rewrite lookup_insert_ne; last lia. by rewrite !tpool_lookup lookup_app_l.
    - by rewrite lookup_insert tpool_lookup lookup_app_r // Nat.sub_diag.
    - rewrite lookup_insert_ne; last lia.
      rewrite !tpool_lookup ?lookup_ge_None_2 ?length_app //=;
         change (ofe_car exprO) with expr; lia.
  Qed.

  Lemma tpool_singleton_included tp j e :
    {[j := Excl e]} ≼ to_tpool tp → tp !! j = Some e.
  Proof.
    move=> /singleton_included_l [ex [/leibniz_equiv_iff]].
    rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included ?]. by f_equal.
  Qed.
  Lemma tpool_singleton_included' tp j e :
    {[j := Excl e]} ≼ to_tpool tp → to_tpool tp !! j = Excl' e.
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.
End conversions.

Section to_heap.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L V.
  Implicit Types m : gmap L gname.

  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(1%Qp, to_agree (v:leibnizO V))]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma heap_singleton_included σ l q v :
    {[l := (q, to_agree v)]} ≼ to_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included_l=> -[[q' av] []].
    rewrite /to_heap lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.

  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case: (σ !! l). Qed.

End to_heap.

Section pointsto.
  Context `{!cfgSG Σ}.

  Global Instance pointstoS_fractional l v : Fractional (λ q, l ↦ₛ{q} v)%I.
  Proof.
    intros p q. rewrite heapS_pointsto_eq -own_op -auth_frag_op.
    by rewrite -pair_op singleton_op -pair_op agree_idemp right_id.
  Qed.
  Global Instance pointstoS_as_fractional l q v :
    AsFractional (l ↦ₛ{q} v) (λ q, l ↦ₛ{q} v)%I q.
  Proof. split. done. apply _. Qed.
  Global Instance frame_pointstoS p l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (l ↦ₛ{q1} v) (l ↦ₛ{q2} v) (l ↦ₛ{q} v) | 5.
  Proof. apply: frame_fractional. Qed.

  Lemma pointstoS_agree l q1 q2 v1 v2 : l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply bi.entails_wand, bi.wand_intro_r.
    rewrite heapS_pointsto_eq -own_op -auth_frag_op own_valid uPred.discrete_valid.
    f_equiv=> /=.
    rewrite -pair_op singleton_op right_id -pair_op.
    rewrite auth_frag_valid pair_valid.
    intros [_ Hv]. move:Hv => /=.
    rewrite singleton_valid.
    by move=> [_] /to_agree_op_inv_L [->].
  Qed.

  Lemma pointstoS_valid l q v : l ↦ₛ{q} v -∗ ✓ q.
  Proof.
    rewrite heapS_pointsto_eq /heapS_pointsto_def own_valid !uPred.discrete_valid.
    apply bi.entails_wand, pure_mono=> /auth_frag_valid /= [_ Hfoo].
    revert Hfoo. simpl. rewrite singleton_valid.
    by intros [? _].
  Qed.

  Lemma pointstoS_valid_2 l q1 q2 v1 v2 : l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (pointstoS_agree with "H1 H2") as %->.
    iApply (pointstoS_valid l _ v2). by iFrame.
  Qed.

  Global Instance pointstoS_combine_sep_gives l dq1 dq2 v1 v2 :
    CombineSepGives (l ↦ₛ{dq1} v1) (l ↦ₛ{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]". iSplit.
    - iDestruct (pointstoS_valid_2 with "H1 H2") as %?; auto.
    - iDestruct (pointstoS_agree with "H1 H2") as %?; auto.
  Qed.

  Lemma pointstoS_half_combine l v1 v2 :
    l ↦ₛ{1/2} v1 -∗ l ↦ₛ{1/2} v2 -∗ ⌜v1 = v2⌝ ∗ l ↦ₛ v1.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (pointstoS_agree with "Hl1 Hl2") as %?. simplify_eq.
    iSplit; eauto. iCombine "Hl1 Hl2" as "?". done.
  Qed.

End pointsto.
