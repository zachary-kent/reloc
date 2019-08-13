(* ReLoC -- Relational logic for fine-grained concurrency *)
(** A resource algebra for the specification programs. *)
From iris.algebra Require Import auth excl gmap agree list frac.
From iris.bi Require Export fractional.
From iris.base_logic Require Export gen_heap invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang lifting.
Import uPred.

Definition relocN := nroot .@ "reloc".
Definition specN := relocN .@ "spec".

(** The CMRA for the heap of the specification. *)
Definition tpoolUR : ucmraT := gmapUR nat (exclR exprO).
Definition cfgUR := prodUR tpoolUR (gen_heapUR loc val).

(** The CMRA for the thread pool. *)
Class cfgSG Σ := CFGSG { cfg_inG :> inG Σ (authR cfgUR); cfg_name : gname }.
Class relocG Σ := RelocG {
  relocG_heapG :> heapG Σ;
  relocG_cfgG :> cfgSG Σ;
}.

Definition to_tpool (tp : list expr) : tpoolUR := Excl <$> (map_seq 0 tp).

Section definitionsS.
  Context `{cfgSG Σ, invG Σ}.

  Definition heapS_mapsto_def (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own cfg_name (◯ (∅, {[ l := (q, to_agree v) ]})).
  Definition heapS_mapsto_aux : { x | x = @heapS_mapsto_def }. by eexists. Qed.
  Definition heapS_mapsto := proj1_sig heapS_mapsto_aux.
  Definition heapS_mapsto_eq :
    @heapS_mapsto = @heapS_mapsto_def := proj2_sig heapS_mapsto_aux.

  Definition tpool_mapsto_def (j : nat) (e: expr) : iProp Σ :=
    own cfg_name (◯ ({[ j := Excl e ]}, ∅)).
  Definition tpool_mapsto_aux : { x | x = @tpool_mapsto_def }. by eexists. Qed.
  Definition tpool_mapsto := proj1_sig tpool_mapsto_aux.
  Definition tpool_mapsto_eq :
    @tpool_mapsto = @tpool_mapsto_def := proj2_sig tpool_mapsto_aux.

  Definition mkstate (σ : gmap loc val) (κs : gset proph_id) :=
    {| heap := σ; used_proph_id := κs |}.
  Definition spec_inv ρ : iProp Σ :=
    (∃ tp σ, own cfg_name (● (to_tpool tp, to_gen_heap (heap σ)))
                 ∗ ⌜rtc erased_step ρ (tp,σ)⌝)%I.
  Definition spec_ctx (ρ : cfg heap_lang) : iProp Σ :=
    inv specN (spec_inv ρ).

  Global Instance heapS_mapsto_timeless l q v : Timeless (heapS_mapsto l q v).
  Proof. rewrite heapS_mapsto_eq. apply _. Qed.
  Global Instance tpool_mapsto_timeless j e: Timeless (tpool_mapsto j e).
  Proof. rewrite tpool_mapsto_eq. apply _. Qed.
  Global Instance spec_ctx_persistent ρ : Persistent (spec_ctx ρ).
  Proof. apply _. Qed.
End definitionsS.
Typeclasses Opaque heapS_mapsto tpool_mapsto spec_ctx.

Notation "l ↦ₛ{ q } v" := (heapS_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope.
Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : bi_scope.
Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.

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
  Hint Resolve tpool_lookup_Some.

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
      rewrite !tpool_lookup ?lookup_ge_None_2 ?app_length //=;
         change (ofe_car exprO) with expr; lia.
  Qed.

  Lemma tpool_singleton_included tp j e :
    {[j := Excl e]} ≼ to_tpool tp → tp !! j = Some e.
  Proof.
    move=> /singleton_included [ex [/leibniz_equiv_iff]].
    rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included ?]. by f_equal.
  Qed.
  Lemma tpool_singleton_included' tp j e :
    {[j := Excl e]} ≼ to_tpool tp → to_tpool tp !! j = Excl' e.
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.
End conversions.

Section mapsto.
  Context `{cfgSG Σ}.

  Global Instance mapsto_fractional l v : Fractional (λ q, l ↦ₛ{q} v)%I.
  Proof.
    intros p q. rewrite heapS_mapsto_eq -own_op -auth_frag_op.
    by rewrite -pair_op op_singleton -pair_op agree_idemp right_id.
  Qed.
  Global Instance mapsto_as_fractional l q v :
    AsFractional (l ↦ₛ{q} v) (λ q, l ↦ₛ{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Lemma mapsto_agree l q1 q2 v1 v2 : l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply bi.wand_intro_r.
    rewrite heapS_mapsto_eq -own_op -auth_frag_op own_valid uPred.discrete_valid.
    f_equiv=> /=.
    rewrite -pair_op op_singleton right_id -pair_op.
    move=> [_ Hv]. move:Hv => /=.
    rewrite singleton_valid.
    by intros [_ ?%agree_op_invL'].
  Qed.

  Lemma mapsto_valid l q v : l ↦ₛ{q} v -∗ ✓ q.
  Proof.
    rewrite heapS_mapsto_eq /heapS_mapsto_def own_valid !uPred.discrete_valid.
    apply pure_mono=> /auth_frag_valid /= [_ Hfoo].
    revert Hfoo. simpl. rewrite singleton_valid.
    by intros [? _].
  Qed.

  Lemma mapsto_valid_2 l q1 q2 v1 v2 : l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ✓ (q1 + q2)%Qp.
  Proof.
    iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %->.
    iApply (mapsto_valid l _ v2). by iFrame.
  Qed.

  Lemma mapsto_half_combine l v1 v2 :
    l ↦ₛ{1/2} v1 -∗ l ↦ₛ{1/2} v2 -∗ ⌜v1 = v2⌝ ∗ l ↦ₛ v1.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (mapsto_agree with "Hl1 Hl2") as %?. simplify_eq.
    iSplit; eauto.
    iApply (fractional_half_2 with "Hl1 Hl2").
  Qed.

End mapsto.
