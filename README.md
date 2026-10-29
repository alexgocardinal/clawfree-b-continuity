# Claw-free b-continuity counterexample

Alex Chan, Harvard University and NBER  
achan@hbs.edu

## Result

The Lean development defines a simple claw-free graph on 12 vertices with
b-colorings using four and six colors, and proves that no b-coloring with
five colors exists. Consequently, its b-spectrum is not an interval.

The graph is the simple line graph of K(3,3) with each edge of one perfect
matching doubled. Vertices 0 through 8 are the root positions in row-major
order; vertices 9, 10, 11 are the second copies at the diagonal positions.
Distinct vertices are adjacent exactly when their root positions share a
row or a column.

## Reproduce the verification

Install Elan, then run these commands from this directory:

```bash
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean 4.19.0 and Mathlib v4.19.0 are pinned in the configuration files.
The dependency manifest records the resolved revisions.

The main theorem is `Clawfree.Base.counterexample`. The five-color
exclusion checks all 390625 normalized assignments and proves, using an
explicit bijection of the palette, that normalization covers every
possible five-color b-coloring.

## Verification scope and trust

The formal theorem concerns the 12-vertex counterexample.
The finite checks use `native_decide`, which relies on Lean's native
compiler. The reported theorem dependencies are:

- `propext`
- `Classical.choice`
- `Lean.ofReduceBool`
- `Quot.sound`

The audit reports no `sorryAx` placeholder. This is a compiler-trusting
Lean verification; it is not a claim of kernel-only reduction.
No historical-priority or minimum-order claim is made.

AI tools assisted with development and drafting.
