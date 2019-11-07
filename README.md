# ReLoC

This is the Coq development of [ReLoC](https://cs.ru.nl/~dfrumin/reloc/).
It consists of the formalization of all the logical rules, tactics, and examples.

## Usage guide

See the small ReLoC [docs/guide.md](docs/guide.md) and the Iris [ProofGuide.md](https://gitlab.mpi-sws.org/iris/iris/blob/master/ProofGuide.md).

## Building

This project has been tested with Coq 8.10.1.

### OPAM

Make sure that you have Iris OPAM repository enabled:

    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Then install the ReLoC development as usual:

    opam install .

### Manually

Install the development versions of [Iris](https://gitlab.mpi-sws.org/iris/iris/), [std++](https://gitlab.mpi-sws.org/iris/stdpp), and a [coq86-devel](https://github.com/uds-psl/autosubst/tree/coq86-devel) branch of Autosubst.

Run `make` and `make install`.

## Examples

We have formalized a variety of different examples in ReLoC. Hopefully
they can illustrate the usage of the logic.

- `lib`
  + `Y.v` - symbolic execution rules and refinements for different fixed point combinators
  + `lock.v` - symbolic execution rules for a simple spin lock
  + `counter.v` - symbolic execution rules and refinements for two different counters
  + `list.v` - rules for the recursive type of lists
- `examples`
  + `bit.v` - "representation independence example" for a simple bit interface
  + `or.v` - expressing non-determinism with concurrency
  + `symbol.v` and `namegen.v` - generative ADTs for symbol and name generation
  + `stack/refinement.v` - Treiber stack refines sequential stack
  + `cell.v` - higher-order cell objects
  + `ticket_lock.v` - ticket lock refines spin lock
  + `various.v` - lots of examples with higher-order functions with local state, in the style of "The effects of higher-order state and control on local relational reasoning" paper
- `experimental` more "experimental" stuff
  + `helping/helping_stack.v` linearizability of stack with helping

## Differences with the old version

This version (ReLoC v2) is build directly on top of heap_lang of [Iris](https://gitlab.mpi-sws.org/iris/iris/), instead of having an ad-hoc object language.
It should be easy to port the existing programs to heap_lang.
The main differences is the absence of `Pack` and `Fold` constructors (the existential types are given transparently, and for recursive types you only need an unfolding function `rec_unfold`, see e.g. `examples/stack/CG_stack.v`).

On the level of logic, the main proposition is now of the form

    REL e1 << e2 @ E : A

We found it beneficial to get rid of the typing environments Γ and Δ, because usually we want to reason about closed programs at the top level anyway.
The type `A` is now not a syntactic construction, but a relation `A : lrel Σ` in logic over the type of values.
The syntax for the `REL` proposition was also adjusted to match the syntax of `WP` more closely.

The old logical judgment `{Δ;Γ;E} ⊧ e1 ≤log≤ e2 : τ` is redefined on top of the `REL` proposition.
See the files `typing/interp.v` and `typing/soundness.v`.

For more information see the [guide](docs/guide.md).
