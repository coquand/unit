LAZY in indexed Unit
====================

This development formalises the intersection semantics of
../doc/lazy-intersection.tex. From the unit-indexed directory, run:

  cabal build exe:seg
  cabal run seg -- lazy/All.seg

Checked on 2026-11-05: 1535 declarations, zero failures, including seven
conversion checks for Example 4. All.seg imports the complete development.
The proof uses the existing checker without adding axioms or postulates.

Proof organisation
------------------

Types.seg and Subtyping.seg define finite intersection types and their
declarative order. The information order is reversed: u is below v as an
element when v <= u as a type. omega represents least information; meet of
types corresponds to joining compatible finite elements.

Arrow.seg proves beta-soundness directly by a filter interpretation of
result obligations. This avoids introducing a second subtyping algorithm
and proving cut elimination. ArrowShape.seg supplies both directions of
arrow inversion, including the top-codomain case. ProductInverse.seg and
AtomInverse.seg give the corresponding product and atom results.

Observations.seg defines cell observations and binding observations as two
query sorts of one indexed inductive family. ObsGeneration.seg gives the
generation lemma. ObsEnvironment.seg supplies strengthening, and
ObsBindings.seg merges choices of types for captured bindings by finite
meets. These meets require no consistency proof.

InvarianceLFull.seg proves both directions of the circular LABEL rewrite.
The remaining Invariance*.seg and Allocation*.seg modules prove the other
rewrite cases. Invariance.seg combines them:

  stepInvariant: a rewrite preserves all observations at old addresses.
  traceInvariant: a finite sequence of rewrites has the same property.

Both combined theorems take WfHeap for the initial heap. HeapSupport.seg
proves that rewrites preserve this condition and preserve defined addresses.
SemanticEquivalence.seg states precisely which observations are preserved.

PartialCorrectness.seg combines trace invariance with terminality of an
evaluation. quotedSound and quotedComplete characterise exactly the types
of an initial cell whose evaluation returns a quoted atom. The theorem
quotedResultsUnique proves that two terminating evaluations returning
quoted atoms return the same atom. FinalForms.seg supplies the pair and
closure shape and separation lemmas.

Example4.seg supplies an explicit 21-step rewrite trace and a derivation
following the lazy demand schedule. Conversion verifies that the trace
extracted from the evaluation derivation equals the explicit trace, and
that its final root contains the quoted numeral 1. It includes allocation
and an actual circular LABEL binding. Example4Support.seg proves the initial
heap is well formed. Example4Correctness.seg proves that the original root
has exactly the types above the singleton type for 1.

Assumptions and scope
---------------------

The inductive definitions remain strictly positive. Contravariance in the
arrow rule exchanges the indices of a subtyping premise; it does not place
the inductive family in a negative position. Recursive observation premises
are direct positive occurrences. No approximation stage or semantic
consistency premise is needed.

Allocation requires a separate structural condition: WfHeap means that
every pointer in a defined cell refers to a defined cell, including pointers
in captured bindings. Merely requiring fresh allocation addresses would
allow allocation to give new observations to an old dangling pointer.
Thus the note's invariance and partial-correctness statements should be read
with this heap condition and with preservation restricted to old addresses.
The nonallocating rewrite proofs establish the stronger statement for all
queries without WfHeap. This structural condition is distinct from semantic
consistency of types; inconsistent intersection types are still allowed.

Eval.seg describes evaluation by a positive big-step relation, Evaluates.
A derivation is a certified terminating execution, from which evalTrace
computes a rewrite trace and evalTerminal proves terminality. Recursive
demands recheck the rewrite guards to accommodate cyclic aliasing. This is
not a general executable search procedure or a termination theorem.

The proved correctness is in the intersection semantics. An isomorphism
between its ideal completion and the paper's Scott domain is not formalised
here, nor is the dependent MIN extension.

Checking times
--------------

After building the checker, reproduce the comparison with:

  python3 lazy/benchmark.py

The script checks All.seg in three fresh Unit processes. It checks the Agda
endpoints LAZY.Example4, LAZY.InvarianceL, LAZY.InvarianceLBack and LAZY.ObsInv
in three independent temporary copies of ~/DOMAIN/LAZY without cached
interfaces. The original Agda files are not modified. Compiler build time
is excluded. Commands, outputs, times, Unit source hashes and the checker
binary hash are recorded in benchmark.json.

Measured medians on 2026-11-05:

  Unit:                   0.237 seconds
  Agda 2.8.0, cold check:  5.088 seconds

These are whole-development checking times, not a controlled language
performance comparison. The presentations and theorem coverage differ:
the Agda endpoints do not supply the allocating rewrite cases or the
certified execution trace now included in the Unit development.
