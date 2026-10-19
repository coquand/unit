SAG Theorem 3.3.3: every f : Spec A -> N is merely bounded
==========================================================

Check from the repository root:   ./segc sag/bounded all

Main.theorem (Bridge.seg):
    (f : Spec A -> N) -> || (N : N) * ((x : Spec A) -> f x <= N) ||

Hypotheses of Main, beyond the foundation of ../replacement (univalence,
replacement; funext and truncation derived):
  setR     R is a set
  one-nz   1 /= 0                                    (from Loc)
  sqc-AT   SQC for A[T], surjectivity: every function Spec(A[T]) -> R is
           merely evaluation at a polynomial over A
  sqc-RT   SQC for R[T], injectivity: polynomials over R with the same
           evaluation function have the same coefficients

A is any R-algebra (a ring with a map from R); finite presentation only
licenses the two SQC instances and is not otherwise used.

Proof (no tensor product, no eventually vanishing sequences):
  Bounded.seg  the coefficient argument.  H (x, t) = t^(f x) is merely the
               evaluation of ONE polynomial p over A; at each x, x(p) and
               T^(f x) have the same evaluation, so the same coefficients;
               if f x >= length p the coefficient at f x gives 1 = 0.
               The bound is the length of p.
  Bridge.seg   A[T] (coefficient lists over A, sag/Mul.seg operations),
               Spec(A[T]) as the R-algebra maps that respect coefficient
               equality, and spec-AT : Spec(A[T]) ~ Spec A * R
               (y |-> (a |-> y [a], y T), inverse (x, t) |-> (p |-> x(p)(t))).
               Main derives Bounded's hypothesis on Spec A * R from sqc-AT.

Not formalised: finitely presented algebras in general, and the
statement of sqc-RT as SQC for R[T] through Spec(R[T]) ~ R (the case
A = R of spec-AT).

Links: Base, Prelude, Paths, Axioms, FunExtUA -> ../core;
Replacement, Truncation -> ../replacement; Ring, Poly, Roots, Group,
Mul -> ../sag.  None of these is modified.
