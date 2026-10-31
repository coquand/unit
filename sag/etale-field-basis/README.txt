Finite basis from a finite algebra presentation and finite spanning data
======================================================================

1. Checked final theorem

FinitePresentedFieldBasis.Over[R,setR,dec].At[S].theorem fp finite

Inputs:
  R is a commutative set-ring;
  dec(r) says either r=0 or provides w with r*w=1;
  S is an R-algebra;
  fp : Presentations.Over[R,setR].FP S;
  finite : FiniteSpan.Over[R,S.ring,S.iota].Finite.

Conclusion:
  merely (d : Nat) together with
    TraceBasis.Over[R,setR,S].Basis[d].

This is an actual basis: finite vectors, R-linear coordinates,
reconstruction of every element, and Kronecker coordinates of the
vectors. It is stronger than finite spanning data. The theorem does
not assume a finite relation matrix, a basis, a finite-free cover, or
finite generation of a module kernel. All of these are constructed.
The zero ring is allowed: the theorem needs the displayed zero-or-unit
law, not a separate proof that 0 and 1 differ.

2. Proof and interfaces

FiniteSpanIntegral, reused from etale-field-generated, applies the
checked determinant trick to choose a monic annihilator for each
algebra generator. Only this finite family is chosen, under truncation.

MonicBasisUniversal.Over[R,setR].At[cs] constructs the quotient by the
monic polynomial with lower coefficient list cs. It reuses the unique
monic-remainder basis from chatelet/EtaleBasis and EtaleFreeLinear.
It exports Q, x, degree, basis, root, To[S,y,hy].hom and beta,
and unique for algebra maps agreeing on x. Horner values end in 1;
the empty list therefore gives the degree-zero relation 1=0.

FiniteBasisComposition.Over[R,setR,Q,T,n,b,m,c] composes a finite R-basis
of Q with a finite Q-basis of T. Coordinates are nested coordinates,
indexed by the explicit rectangular enumeration; the inverse performs
the two finite linear combinations. Both inverse laws are proved.
LinearCoordinatesBasis converts this linear isomorphism into TraceBasis.

IteratedMonicBasis.Over[R,setR].construct n cs returns Cover[n,cs]:
  algebra, rank, basis, generator;
  extend(S,x,hx), beta(S,x,hx,i);
  unique(S,f,g,h,a), determining maps by their generator values.
It iterates monic quotients and composes the bases. The coefficient
rings need no field, reducedness or nonzero hypotheses. All ranks,
including zero, are permitted.

For the original presentation p, the constructed Q maps onto S:
an expression representing s is evaluated in Q and maps to s.
PresentationKernel, reused from etale-field-presentation-kernel,
proves that the ORIGINAL equations evaluated in Q generate ker(Q->S).
It uses quotient effectiveness and the two universal properties.

FiniteFreeQuotientBasis.Over[R,setR,dec].At
  [Q,S,d,b,u,onto,m,g,killed,kernel]
then supplies rank and basis. The module relations are the finite
family g_j*b_i. Expanding each ideal coefficient in the Q-basis proves
that these relations generate the entire module kernel. GaussianAlgebraBasis,
reused from etale-field-gaussian, constructs the quotient basis.

The final theorem combines these constructions inside the truncations
of the original presentation, finite spanning family and monic equations.
It makes no global choice of representatives or coordinates.

3. Regressions

FieldBasisRegression checks the full final theorem over F2 for:
  the base algebra (no algebra generators);
  the monic dual-number algebra F2[X]/(X^2), which is nonreduced;
  the degree-zero monic quotient F2/(1), with the empty spanning family.

Over Z/4Z it constructs the two-generator monic tower with each
polynomial X^2-X, computes its rank as 4, applies its actual basis
reconstruction, and evaluates its generators at (0,1).
The degree-zero monic tower computes rank 0.

Two isolated mutations were rejected by the checker:
  replacing the final monic Horner coefficient 1 by 0;
  replacing every flattened ideal coefficient by 0.
The second fails the module-kernel combination identity. Working files
were never mutated; these checks ran in separate temporary directories.

4. Files and validation (31 October 2026)

Nine owned proof modules, 318 declarations including 18 open directives:
  FiniteRectangleProperty, FiniteFreeQuotientBasis,
  LinearCoordinatesBasis, MonicTraceBasis, FiniteBasisComposition,
  MonicBasisUniversal, IteratedMonicBasis,
  FinitePresentedFieldBasis, FieldBasisRegression.
All other .seg files are unchanged relative links. No checker changes,
new axioms, shared edits or commits. All.seg uses the existing univalence,
replacement and surjection parameters of the reused developments.

  ./segc sag/etale-field-basis all

Result: 215 modules, 0 failed, 3.51 s.
Fresh built checker on All.seg: 8939 declarations, 0 failed, 4.00 s.
Every owned declaration takes at most 0.02 s and opens at most 26
separate definitions. etale-field-basis.opens covers every one of the
300 named owned declarations; all report "nothing else opened".
The checking server is stopped.

5. Scope

This directory proves finite spanning + finite algebra presentation
implies a finite basis over the zero-or-unit base. It does not itself
prove that an unramified algebra is finite. That theorem is provided
by the separate zero-dimensional finiteness development and integrated
in etale-field/UnramifiedFieldStructure.

Combining this basis with etale-field-trace eliminates the explicit
basis hypothesis from the finite-unramified trace-pairing theorem.
Primitive-element construction over small fields, selecting a prime
factor, and the final coefficient-and-denominator bridge into the local
etale theorem remain separate tasks. No such result is asserted here.
