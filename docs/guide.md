WIP

# Proving contextual refinements

Suppose you have derived `REL e1 << e2 : lrel_int` in the logic.
From this proof you want to derive a *closed contextual refinement proof*

      ∅ ⊨ e1 ≤ctx≤ e2 : TNat

For this, make use of the lemma `refines_sound`:

     eapply (refines_sound relocΣ).

Your proof obligation will then be reduced to showing

     ∀ Δ, REL e1 << e2 : (interp TNat Δ)

where the latter relation computes to `(interp TNat Δ) ≡ lrel_int`.

Suppose you have used some additional CMRAs in your proofs of logical refinement.
Then you need to provide the corresponding functors to the `refines_sound` lemma.
For example, in the `examples/cell.v` file, the logical refinement proof
`REL cell2 << cell1 : ∀ α, ∃ β, (α → β) * (β → α) * (β → α → ())`
made use of the lock specifications and required the `lockG Σ` assumption.
To derive the closed contextual refinement proof we had to use additional functors the soundness lemma:

    pose (Σ := #[relocΣ;lockΣ]).
    eapply (refines_sound Σ).
