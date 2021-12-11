(* ReLoC -- Relational logic for fine-grained concurrency *)
(** Compataibility rules *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Import proofmode.
From reloc.logic Require Export model rules.
From reloc.logic Require Import proofmode.tactics proofmode.spec_tactics model.

Section compatibility.
  Context `{!relocG Σ}.
  Implicit Types e : expr.

  Local Ltac value_case :=
    try rel_pure_l; try rel_pure_r; rel_values.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(Hv):=
    rel_bind_l e1;
    rel_bind_r e2;
    iApply (refines_bind with IH);
    iIntros (v w) Hv; simpl.

  Lemma refines_pair e1 e2 e1' e2' A B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1, e2) << (e1', e2') : A * B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" v2 v2' "Hvv2".
    rel_bind_ap e1 e1' "IH1" v1 v1' "Hvv1".
    value_case.
    iExists _, _, _, _; eauto.
  Qed.

  Lemma refines_app e1 e2 e1' e2' A B :
    (REL e1 << e1' : A → B) -∗
    (REL e2 << e2' : A) -∗
    REL App e1 e2 << App e1' e2' : B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" v v' "Hvv".
    rel_bind_ap e1 e1' "IH1" f f' "Hff".
    by iApply "Hff".
  Qed.

  Lemma refines_seq A e1 e2 e1' e2' B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1;; e2) << (e1';; e2') : B.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e1 e1' "IH1" v v' "#Hvv".
    repeat rel_pure_l. repeat rel_pure_r.
    done.
  Qed.

  Lemma refines_pack (A : lrel Σ) e e' (C : lrel Σ → lrel Σ) :
    (REL e << e' : C A) -∗
    REL e << e' : ∃ A, C A.
  Proof.
    iIntros "H".
    rel_bind_ap e e' "H" v v' "Hvv".
    value_case.
    iModIntro. iExists A. done.
  Qed.

  Lemma refines_forall e e' (C : lrel Σ → lrel Σ) :
    □ (∀ A, REL e << e' : C A) -∗
    REL (λ: <>, e)%V << (λ: <>, e')%V : ∀ A, C A.
  Proof.
    iIntros "#H".
    rel_values. iModIntro.
    iIntros (A ? ?) "_ !#".
    rel_rec_l. rel_rec_r. iApply "H".
  Qed.

  Lemma refines_store e1 e2 e1' e2' A :
    (REL e1 << e1' : ref A) -∗
    (REL e2 << e2' : A) -∗
    REL e1 <- e2 << e1' <- e2' : ().
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" w w' "IH2".
    rel_bind_ap e1 e1' "IH1" v v' "IH1".
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    rel_store_l_atomic.
    iInv (relocN .@ "ref" .@ (l,l')) as (v v') "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro. iExists _; iFrame "Hv1".
    iNext. iIntros "Hw1".
    rel_store_r.
    iMod ("Hclose" with "[Hw1 Hv2 IH2]").
    { iNext; iExists _, _; simpl; iFrame. }
    value_case.
  Qed.

  Lemma refines_xchg e1 e2 e1' e2' A :
    (REL e1 << e1' : ref A) -∗
    (REL e2 << e2' : A) -∗
    REL Xchg e1 e2 << Xchg e1' e2' : A.
  Proof.
    iIntros "IH1 IH2".
    rel_bind_ap e2 e2' "IH2" w w' "IH2".
    rel_bind_ap e1 e1' "IH1" v v' "IH1".
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    rel_xchg_l_atomic.
    iInv (relocN .@ "ref" .@ (l,l')) as (v v') "[Hv1 [>Hv2 #Hv]]" "Hclose".
    iModIntro. iExists _; iFrame "Hv1".
    iNext. iIntros "Hw1".
    rel_xchg_r.
    iMod ("Hclose" with "[Hw1 Hv2 IH2]").
    { iNext; iExists _, _; simpl; iFrame. }
    value_case.
  Qed.

  Lemma refines_load e e' A :
    (REL e << e' : ref A) -∗
    REL !e << !e' : A.
  Proof.
    iIntros "H".
    rel_bind_ap e e' "H" v v' "H".
    iDestruct "H" as (l l' -> ->) "#H".
    rel_load_l_atomic.
    iInv (relocN .@ "ref" .@ (l,l')) as (w w') "[Hw1 [>Hw2 #Hw]]" "Hclose"; simpl.
    iModIntro. iExists _; iFrame "Hw1".
    iNext. iIntros "Hw1".
    rel_load_r.
    iMod ("Hclose" with "[Hw1 Hw2]").
    { iNext. iExists w,w'; by iFrame. }
    value_case.
  Qed.

  Lemma refines_cmpxchg_ref A e1 e2 e3 e1' e2' e3' :
    (REL e1 << e1' : lrel_ref (lrel_ref A)) -∗
    (REL e2 << e2' : lrel_ref A) -∗
    (REL e3 << e3' : lrel_ref A) -∗
    REL (CmpXchg e1 e2 e3) << (CmpXchg e1' e2' e3') : lrel_prod (lrel_ref A) lrel_bool.
  Proof.
    iIntros "IH1 IH2 IH3".
    rel_bind_l e3; rel_bind_r e3'.
    iApply (refines_bind with "IH3").
    iIntros (v3 v3') "#IH3".
    rel_bind_l e2; rel_bind_r e2'.
    iApply (refines_bind with "IH2").
    iIntros (v2 v2') "#IH2".
    rel_bind_l e1; rel_bind_r e1'.
    iApply (refines_bind with "IH1").
    iIntros (v1 v1') "#IH1 /=".
    iPoseProof "IH1" as "IH1'".
    iDestruct "IH1" as (l1 l2) "(% & % & Hinv)"; simplify_eq/=.
    rewrite {2}/lrel_car /=.
    iDestruct "IH2" as (r1 r2 -> ->) "Hr".
    (* iDestruct "IH3" as (n1 n2 -> ->) "Hn". *)
    rel_cmpxchg_l_atomic.
    iInv (relocN .@ "ref" .@ (l1,l2)) as (v1 v2) "[Hl1 [>Hl2 #Hv]]" "Hclose".
    iModIntro. iExists _; iFrame. simpl.
    destruct (decide ((v1, v2) = (#r1, #r2))); simplify_eq/=.
    - iSplitR; first by (iIntros (?); contradiction).
      iIntros (?). iNext. iIntros "Hv1".
      rel_cmpxchg_suc_r.
      iMod ("Hclose" with "[-]").
      { iNext. iExists _, _. by iFrame. }
      rel_values. iExists _, _, _, _. do 2 (iSplitL; first done).
      iFrame "Hv". iExists _. done.
    - iSplit; iIntros (?); simplify_eq/=; iNext; iIntros "Hl1".
      + destruct (decide (v2 = #r2)); simplify_eq/=.
        * rewrite {5}/lrel_car. simpl.
          iDestruct "Hv" as (r1' r2' ? ?) "#Hv". simplify_eq/=.
          destruct (decide ((l1, l2) = (r1, r2'))); simplify_eq/=.
          { iInv (relocN.@"ref".@(r1', r2')) as (? ?) "(Hr1 & >Hr2 & Hrr)" "Hcl".
            iExFalso. by iDestruct (mapstoS_valid_2 with "Hr2 Hl2") as %[]. }
          destruct (decide ((l1, l2) = (r1', r2'))); simplify_eq/=.
          ++ assert (r1' ≠ r1) by naive_solver.
             iInv (relocN.@"ref".@(r1, r2')) as (? ?) "(Hr1 & >Hr2 & Hrr)" "Hcl".
             iExFalso. by iDestruct (mapstoS_valid_2 with "Hr2 Hl2") as %[].
          ++ iInv (relocN.@"ref".@(r1, r2')) as (? ?) "(Hr1 & >Hr2 & Hrr)" "Hcl".
             iInv (relocN.@"ref".@(r1', r2')) as (? ?) "(Hr1' & >Hr2' & Hrr')" "Hcl'".
             iExFalso. by iDestruct (mapstoS_valid_2 with "Hr2 Hr2'") as %[].
        * rel_cmpxchg_fail_r.
          iMod ("Hclose" with "[-]").
          { iNext; iExists _, _; by iFrame. }
          rel_values. iModIntro. iExists _,_,_,_.
          repeat iSplit; eauto.
      + assert (v2 ≠ #r2) by naive_solver.
        rewrite {5}/lrel_car. simpl.
        iDestruct "Hv" as (r1' r2' ? ?) "#Hv". simplify_eq/=.
        destruct (decide ((l1, l2) = (r1', r2'))); simplify_eq/=.
        { iInv (relocN.@"ref".@(r1', r2)) as (? ?) "(>Hr1 & >Hr2 & Hrr)" "Hcl".
          iExFalso. by iDestruct (mapsto_valid_2 with "Hr1 Hl1") as %[]. }
        destruct (decide ((l1, l2) = (r1', r2))); simplify_eq/=.
        { iInv (relocN.@"ref".@(r1', r2')) as (? ?) "(>Hr1 & >Hr2 & Hrr)" "Hcl".
          iExFalso. by iDestruct (mapsto_valid_2 with "Hr1 Hl1") as %[]. }
        iInv (relocN.@"ref".@(r1', r2)) as (? ?) "(>Hr1 & >Hr2 & Hrr)" "Hcl".
        iInv (relocN.@"ref".@(r1', r2')) as (? ?) "(>Hr1' & >Hr2' & Hrr')" "Hcl'".
        iExFalso. by iDestruct (mapsto_valid_2 with "Hr1 Hr1'") as %[].
  Qed.

End compatibility.

