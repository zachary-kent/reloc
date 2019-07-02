(* ReLoC -- Relational logic for fine-grained concurrency *)
(** A "mailbox" datastructure for helping.
Based on the case study <https://iris-project.org/pdfs/2017-case-study-concurrent-stacks-with-helping.pdf> *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From reloc Require Export reloc.

Definition mk_offer : val :=
  λ: "v", ("v", ref #0).
Definition revoke_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #2 then SOME (Fst "v") else NONE.
Definition take_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #1 then SOME (Fst "v") else NONE.

Definition put_mail : val := λ: "r" "v",
  let: "off" := mk_offer "v" in
  "r" <- SOME "off";;
  revoke_offer "off".
Definition get_mail : val := λ: "r",
  match: !"r" with
    NONE => NONE
  | SOME "x" => take_offer "x"
  end.
Definition new_mb : val := λ: <>, ref NONE.
Definition mailbox : val :=
  (new_mb, put_mail, get_mail).


Definition channelR := exclR unitR.
Class channelG Σ := { channel_inG :> inG Σ channelR }.
Definition channelΣ : gFunctors := #[GFunctor channelR].
Instance subG_channelΣ {Σ} : subG channelΣ Σ → channelG Σ.
Proof. solve_inG. Qed.

Section side_channel.
  Context `{!heapG Σ, !channelG Σ}.
  Implicit Types l : loc.

  Definition stages γ (P : val → iProp Σ) l v :=
    ((l ↦ #0 ∗ P v)
     ∨ (l ↦ #1)
     ∨ (l ↦ #2 ∗ own γ (Excl ())))%I.

  Definition is_offer γ (P : val → iProp Σ) (v : val) : iProp Σ :=
    (∃ v' l, ⌜v = (v', # l)%V⌝ ∗ ∃ ι, inv ι (stages γ P l v'))%I.

  (* A partial specification for revoke that will be useful later *)
  Lemma revoke_works γ P v :
    is_offer γ P v ∗ own γ (Excl ()) -∗
    WP revoke_offer v
      {{ v', (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ P v'') ∨ ⌜v' = InjLV #()⌝ }}.
  Proof.
    iIntros "[#Hinv Hγ]".
    rewrite /is_offer.
    iDestruct "Hinv" as (v' l) "[% Hinv]"; simplify_eq.
    iDestruct "Hinv" as (N) "#Hinv".
    unlock revoke_offer.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv N as "Hstages" "Hclose".
    iDestruct "Hstages" as "[H | [H | H]]".
    - iDestruct "H" as "[Hl HP]".
      wp_cmpxchg_suc.
      iMod ("Hclose" with "[Hl Hγ]").
      iRight; iRight; iFrame.
      iModIntro. wp_pures.
      iLeft. iExists v'; iSplit; auto.
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[H]").
      iRight; iLeft; auto.
      iModIntro. wp_pures.
      iRight; auto.
    - iDestruct "H" as "[Hl H]".
      wp_cmpxchg_fail.
      by iDestruct (own_valid_2 with "H Hγ") as %?.
  Qed.

  (* A partial specification for take that will be useful later *)
  Lemma take_works γ N P v l :
    inv N (stages γ P l v) -∗
    WP take_offer (v, LitV l)%V
      {{ v', (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ P v'') ∨ ⌜v' = InjLV #()⌝ }}.
  Proof.
    iIntros "#Hinv".
    wp_rec. wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv N as "Hstages" "Hclose".
    iDestruct "Hstages" as "[H | [H | H]]".
    - iDestruct "H" as "[H HP]".
      wp_cmpxchg_suc.
      iMod ("Hclose" with "[H]").
      iRight; iLeft; done.
      iModIntro. wp_pures.
      iLeft; auto.
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[H]").
      iRight; iLeft; done.
      iModIntro. wp_pures; eauto.
    - iDestruct "H" as "[Hl Hγ]".
      wp_cmpxchg_fail.
      iMod ("Hclose" with "[Hl Hγ]").
      iRight; iRight; iFrame.
      iModIntro. wp_pures; eauto.
  Qed.

  Lemma mk_offer_works P (v : val) :
    P v -∗
    WP mk_offer v {{ v', ∃ γ, own γ (Excl ()) ∗ is_offer γ P v' }}.
  Proof.
    iIntros "HP".
    wp_rec.
    wp_alloc l as "Hl".
    iApply wp_fupd.
    wp_pures.
    pose proof (nroot .@ "N'") as N'.
    iMod (own_alloc (Excl ())) as (γ) "Hγ". done.
    iMod (inv_alloc N' _ (stages γ P l v) with "[HP Hl]") as "#Hinv'".
    { iNext. rewrite /stages. iLeft. iFrame. }
    iModIntro.
    iExists γ; iFrame.
    unfold is_offer.
    iExists _, _; iSplitR; eauto.
  Qed.

End side_channel.

Section mailbox.
  Context `{!heapG Σ, !channelG Σ}.
  Implicit Types l : loc.

  Definition mailbox_inv (P : val → iProp Σ) (v : val) : iProp Σ :=
    (∃ l : loc, ⌜v = # l⌝ ∗ (l ↦ NONEV ∨ (∃ v' γ, l ↦ SOMEV v' ∗ is_offer γ P v')))%I.

  Theorem new_mb_works (P : val → iProp Σ) (Φ : val → iProp Σ) :
    (∀ v N, inv N (mailbox_inv P v) -∗ Φ v)
    -∗ WP new_mb #() {{ Φ }}.
  Proof.
    iIntros "HΦ".
    unlock new_mb.
    wp_rec.
    iApply wp_fupd.
    wp_alloc r as "Hr".
    pose proof (nroot .@ "N") as N.
    iMod (inv_alloc N _ (mailbox_inv P (# r)) with "[Hr]") as "#Hinv".
    { iExists r; iSplit; try iLeft; auto. }
    iModIntro.
    by iApply "HΦ".
  Qed.

  Theorem put_mail_works (P : val → iProp Σ) (Φ : val → iProp Σ) N (mb v : val) :
    inv N (mailbox_inv P mb) -∗
    P v -∗
    (∀ v', ((∃ v'', ⌜v' = SOMEV v''⌝ ∗ P v'') ∨ ⌜v' = NONEV⌝) -∗ Φ v')
    -∗ WP put_mail mb v {{ Φ }}.
  Proof.
    iIntros "#Hinv HP HΦ".
    wp_rec.
    wp_pures.
    wp_bind (mk_offer v).
    iApply (wp_wand with "[HP]").
    { iApply (mk_offer_works with "HP"). }
    iIntros (off). iDestruct 1 as (γ) "[Hγ #Hoffer]".
    wp_let.
    wp_bind (mb <- _)%E. wp_pures.
    iInv N as "Hmailbox" "Hclose".
    iDestruct "Hmailbox" as (l) "[>% Hl]". simplify_eq/=.
    iDestruct "Hl" as "[>Hl | Hl]";
      [ | iDestruct "Hl" as (off' γ') "[Hl Hoff']"]; (* off' - already existing offer *)
      wp_store;
      [iMod ("Hclose" with "[Hl]") | iMod ("Hclose" with "[Hl Hoff']")];
      try (iExists _; iNext; iSplit; eauto);
      iModIntro;
      wp_pures;
      iApply (wp_wand with "[Hγ Hoffer] HΦ");
      iApply (revoke_works with "[$]").
  Qed.

  Theorem get_mail_works (P : val → iProp Σ) (Φ : val → iProp Σ) N (mb : val) :
    inv N (mailbox_inv P mb) -∗
    (∀ v', ((∃ v'', ⌜v' = SOMEV v''⌝ ∗ P v'') ∨ ⌜v' = NONEV⌝) -∗ Φ v')
    -∗ WP get_mail mb {{ Φ }}.
  Proof.
    iIntros "#Hinv HΦ".
    unlock get_mail.
    wp_rec.
    wp_bind (! _)%E.
    iInv N as "Hmailbox" "Hclose".
    iDestruct "Hmailbox" as (l') "[>% H]"; simplify_eq/=.
    iDestruct "H" as "[H | H]".
    + wp_load.
      iMod ("Hclose" with "[H]").
      iExists l'; iSplit; auto.
      iModIntro.
      wp_pures. iApply "HΦ"; auto.
    + iDestruct "H" as (v' γ) "[Hl' #Hoffer]".
      wp_load.
      iMod ("Hclose" with "[Hl' Hoffer]").
      { iExists l'; iSplit; auto.
        iRight; iExists v', γ; by iSplit. }
      iModIntro.
      wp_pures.
      iDestruct "Hoffer" as (v'' l'') "[% Hoffer]"; simplify_eq.
      iDestruct "Hoffer" as (ι) "Hinv'".
      iApply (wp_wand with "[] HΦ").
      iApply take_works; auto.
  Qed.

End mailbox.
