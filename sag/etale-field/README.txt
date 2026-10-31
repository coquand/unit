Finite basis and perfect trace for unramified field algebras
==========================================================

1. Main checked theorem

UnramifiedFieldStructure.Over[k,setk,dec,nontrivial].At[S,fp,unique]

Inputs:
  k             a commutative set-ring;
  dec           for every a:k, either a=0 or an explicit inverse;
  nontrivial    1 != 0;
  S             a commutative set-valued k-algebra;
  fp            merely a finite algebra presentation of S;
  unique        FormallyEtale.Unique S: uniqueness of square-zero lifting.

Exports:
  finite        merely a fixed finite spanning family over k;
  basis         merely a dimension d and actual finite basis;
  theorem       merely a Structure with
                  dimension,
                  coordinates : TraceBasis.Basis[dimension],
                  duality : TraceDuality.Certificate,
                  perfect : unit(det(trace-pairing matrix)).

TraceBasis includes actual coordinate functions, their linear laws,
reconstruction and the values on basis vectors. Thus this is not a
claim that mere finite generation automatically produces a basis.
The duality certificate provides the cofactors for
  a = sum_j Tr(a*b_j)*c_j.
The target S may be the zero algebra; dimension zero is allowed.

No ZMT, flatness-transfer principle, finite basis, polynomial kernel
oracle, tensor-coordinate theorem, or primitive element is assumed.
There are no new axioms. All.seg has the existing univalence,
replacement, and surjection parameters used throughout the library.

2. Proof dependencies

etale-field-diagonal:
  Construct the presented tensor diagonal, J=J^2 directly from Unique,
  then the averaging idempotent by the determinant lemma.
etale-field-transfer:
  Construct flat base change and the averaging retraction; transfer
  R-flatness of T to S-flatness for a map from an FP unramified S.
etale-field-regularity:
  Every k-algebra is k-flat by explicit finite-relation explanations.
  Apply transfer to S/(a), deduce a=a^2*b, reducedness and dimension zero.
etale-field-finite, etale-field-monomials, etale-field-generated:
  Construct a rooted nonempty sparse relation, make it monic by a
  triangular Nagata change, and induct on algebra generators. The image
  subalgebra is zero-dimensional by integral descent. Compose spans.
  This finite-span result needs finite generation, not finite presentation.
etale-field-gaussian, etale-field-presentation-kernel, etale-field-basis:
  Determinant annihilators give an iterated monic finite-free cover Q.
  The original presentation equations generate ker(Q->S); their products
  with the Q-basis generate the module kernel. Gaussian elimination gives
  the actual S-basis. All finite choices stay under truncation.
etale-field-trace:
  Construct tensor coordinates from the basis; extract trace duality and
  a matrix inverse from the diagonal idempotent.

UnramifiedFieldStructure only assembles these checked results. All reused
sources are relative links; the underlying developments are unchanged.

3. Validation

Fresh All.seg --opened: 11255 declarations, 0 failed, 4.88 s.
./segc sag/etale-field all: 274 modules, 0 failed.
Two owned files: 45 declarations; each rounds to 0.00 s and opens at most
8 definitions. The .opens audit covers all 42 named declarations (three
anonymous opens omitted), each with nothing else opened.

FieldStructureRegression applies the assembled theorem to F2 itself and
to the actual standard quadratic F2[X]/(X^2-X), using its presentation and
formal unramifiedness. Its distinguished generator is proved nonzero.
The imported milestone regressions cover zero algebras, zero ranks,
nonreduced targets, small fields, multivariable monic covers, signs,
weights, finite matrix kernels and quotient representatives. Each
milestone README records its mutation tests and exact opening audit.

4. Completed field case and remaining local work

This completes the finite-span, finite-basis and perfect-trace outputs.
The separable monogenic neighbourhood at a specified decidable prime is
now also checked, in etale-field-complete. Its main theorem is
UnramifiedFieldSelected.Over[k,setk,field].At[S,fp,unique,q].theorem.
It constructs the basis and exact SelectedFactorStatement.Selected
certificate from these hypotheses; no field-case principle is assumed.

Further checked components:
  etale-field-finite-primitive: an enumerated finite field has an actual
    primitive element, polynomial representatives, and the separable
    annihilator T^q-T; no order or factorisation principle is assumed;
  etale-field-small-branch: the exact selected certificate from the actual
    finite coefficient field and monic equations of the basis vectors;
  etale-field-selected-gaussian, etale-field-selected-basis: construct a
    relative basis after one idempotent refinement outside the prime;
  etale-field-selected-separable: selected simple-root monic equations
    for one element or a finite family, through relative trace and actual
    dual-number derivations, without a discriminant identity;
  etale-field-tensor-separation: an inverse of Delta z off the diagonal
    gives the coordinate identities for selected primitive generation.

The large-field separator search is checked: a polynomial with
unimodular content in the full tensor algebra, polynomial and matrix
McCoy, a bounded determinant, and the polynomial root bound. It avoids
constructing universal splitting algebras. The final bounded-coefficient
dichotomy and theorem assembly check in etale-field-selected-complete.
FiniteMonicCoefficientFamily constructs the monic equations and their
coefficient family before the dichotomy, so the small branch does not
assume supplied equations over an unknown coefficient subfield.

Checked bridge preparations are separate:
  etale-field-basechange: actual scalar extension by mapped presentation,
    preservation of FP and Unique, and mapping-out universal property;
  etale-field-local-interface: the local proof consumes one selected
    factor and representations of only the finite module generators;
  etale-field-fibre: actual residue field, mapped presentation and Unique
    on the actual E/IE, and its module finiteness over R/I;
  etale-field-clearing: pullback equations from (B/I)[1/s] carry explicit
    powers of s, and a quasi-inverse of s gives mere surjectivity of B;
  etale-field-selected-lift: a supplied selected field certificate, with
    the compatible prime/quasi-inverse/local ZMT data, is lifted into the
    exact local theorem; finite coefficient lifts and ideal-witness
    conversions are constructed.
  etale-field-local-complete: the field theorem now constructs that basis
    and selected certificate, from FP and Unique of the exact localized
    fibre and the field structure of the residue quotient. The compatible
    prime, quasi-inverse and local ZMT data remain explicit.
These are not yet a complete construction of the field inputs to the
local theorem. In particular B/mB is never assumed to inject into its
localisation. The full unconditional local flat+unramified=>etale theorem
still requires the remaining connections supplying the explicit bridge
inputs. The selected-prime existence theorem itself is now proved.

Nothing is committed. No checker or shared source was modified.
