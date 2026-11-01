Shortened local proof: integral monogenic fractions give a monic standard chart
=============================================================================

1. Status and scope

The replacement ending of the local etale proof is checked. Starting
with the integral element and polynomial fraction-generation data
available after the determinant argument, it constructs a simple monic
relation and a monic standard presentation of the principal localisation.
The derivative-ideal witness and both finite kernels are constructed,
not assumed. The old gcd/Nakayama degree-lowering loop is not needed.

This is only the local shortcut requested for this milestone. The
finite cover by monic one-variable standard algebras is not constructed.
The earlier finite-subalgebra, residue-field and determinant arguments
that produce the input data remain separate. The old etale-local/Local.seg
has not been rewritten; the new public theorem provides its replacement
ending once those data are supplied.

2. Public theorem

ShortLocalEtale.Over[R,setR,cs].At[E,y,full,unique]
  .theorem fp integral smooth
  .flat-theorem fp integral flat

Inputs:
  R: any commutative set-ring, including the zero ring;
  E: an R-algebra;
  y: an element of E;
  cs: a coefficient list for G in R[T];
  full: for every e in E, merely a polynomial A and n in Nat such that
        A(y) = G(y)^n e (PolynomialFractions.At.Full);
  unique: formal unramifiedness of E (FormallyEtale.Unique);
  fp: merely a finite presentation of E (Presentations.FP);
  integral: merely a coefficient list lower with
            (T^length(lower) + sum lower_i T^i)(y) = 0;
  smooth: square-zero lifting for E (FormallyEtale.Lift), or
  flat: R-flatness in the existing finite-relation sense.

The flat variant calls the unchanged FlatUnramifiedEtale theorem to
supply smooth. G(y) is not required to be a unit in E.

Output, under Truncation[l+]:
  (loc : AffineInterface.LocalizationWitness E G(y)) *
  (lower : List R.R) * (D : R[T]) *
  StandardEtale.Points[monic lower,D].Standard loc.1.

Thus the result contains the actual localisation and its algebra
universal property, a monic Q given by its lower coefficient list, and
the standard presentation E[1/G(y)] = (R[T]/Q)[1/(D Q')]. The Standard
predicate is the existing algebra universal property, not just a
surjective map. Both fp and integral can remain under truncation;
all finite choices are eliminated into the truncated conclusion.

For an already localised E with G(y) invertible, use:
  MonogenicStandard.Over[R,setR,cs].At[
    E,p,pe,y,unit,full,unique,lower,root]
    .simple-relation : merely H,N with H(y)=0 and H'(y)=G(y)^N;
    .simple-monic : merely a monic Q with Q(y)=0 and Q'(y) a unit;
    .Smooth[smooth].theorem : merely a monic standard presentation;
    .Flat[flat].theorem : the same result using R-flatness.

Here p,pe and lower,root are actual presentation and integral witnesses.
Simple-monic needs only unramifiedness; smoothness/flatness is used for
the subsequent removal of the standard source's kernel.

3. Proof and modules

FiniteSurjectionKernel: a surjection between finitely presented
R-algebras has a merely given finite kernel-generating list. Preimages
of the target generators and polynomial expressions for the images of
the source generators are chosen only finitely, inside truncation.

PolynomialLocalisation, PolynomialFractions: construct R[T,1/G], its
finite presentation, maps, polynomial numerators and fraction arithmetic.
The source maps onto E when G(y) is a unit and full holds.

MonicDualTest, MonogenicDerivativeIdeal: construct polynomial kernel
relations F_j. In C = E/(F'_j(y)), the assignment y -> y+epsilon defines
a map E -> C[epsilon]/epsilon^2. Formal unramifiedness forces its
epsilon component to vanish. Thus 1=0 in C, yielding actual finite
coefficients b_j with 1 = sum b_j F'_j(y), under truncation.

SimplePolynomialRelation: lift those coefficients to polynomial
fractions and clear their denominators. Dual-number fraction arithmetic
simultaneously proves H(y)=0 and H'(y)=G(y)^N for a concrete H and N.

MonicRelation: if Q0(y)=0 is monic and H has a coefficient list of
length k, concatenate that list with the coefficients of Q0^2. This
constructs exactly Q = H + T^k Q0^2, records monicity, and proves
Q(y)=0 and Q'(y)=H'(y). It requires no actual-degree decision and also
works for Q0=1. MonicPowers supplies the monic square.

MonogenicStandard: construct the standard source R[T]/Q[1/(G Q')],
prove its map onto E surjective, construct its finite kernel, and reuse
the unchanged EtaleCase/IdempotentIdeal proof to remove that kernel by
one further polynomial localisation. This preserves Q.

PrincipalEtale: principal localisation preserves the square-zero
uniqueness and lifting properties.

LocalMonogenicStandard: construct E[1/G(y)], transport integrality and
fraction generation to it and apply MonogenicStandard. The output also
retains the localisation universal property.

ShortLocalEtale: public interface with merely given finite presentation
and integrality; exports the smooth and flat forms above.

MonicLocalRegression: regression instances below.

4. Validation

Fresh built checker on All.seg with --opened:
  6795 declarations, 0 failed, 2.78 s.
  679 declarations are new, in the 12 owned proof modules.
  Every named new declaration takes at most 0.01 s and opens at most
  33 definitions in this run.

./segc sag/etale-monic-local all:
  168 modules, 0 failed, 2.37 s.

etale-monic-local.opens freezes the actual opening lists for all 657
named new declarations (the other declaration events are open directives).
The fresh --opens audit reports "nothing else opened" for all 657;
6795 declarations, 0 failed, 3.36 s. Quotient operation aliases that
are opened are recorded honestly in those lists.

The reused etale-direct/All.seg rechecks independently:
  5834 declarations, 0 failed, 2.10 s.

Commands, from unit/:
  ./segc sag/etale-monic-local all
  ./segc sag/etale-monic-local check ShortLocalEtale MonicLocalRegression
  cabal list-bin exe:seg
  <built-checker> sag/etale-monic-local/All.seg --opened
  <built-checker> sag/etale-monic-local/All.seg \
    --opens sag/etale-monic-local/etale-monic-local.opens
  ./segc sag/etale-monic-local stop

5. Regressions and mutations

For the base algebra over any R, y=a, G=t and the repeated input
relation Q0=(T-a)^2, construct the standard localisation at t. Both
smooth and flat routes check. Redundant and empty algebra presentations
also check. The public theorem is exercised with fp and integral under
truncation.

Over Z/4Z, localise at 1, at the nilpotent 2, and at 0. These cases
exercise nonreduced coefficients and zero localised algebras.

Every already constructed monic standard algebra can be fed through
the theorem, starting from the square of its defining monic equation.
This checks the construction with genuine algebra generators.

Concrete denominator arithmetic over Z/4Z: at y=2 take F0=T+2,
F1=2T and derivative-ideal coefficients (3,1). With G=3 these
coefficients have fraction exponents 1 and 2 and numerators 1. The
constructed H has H(y)=0 and H'(y)=3^3=3; the exponent computes to 3.

Three deliberate mutations in isolated temporary copies were rejected:
  - replace Q0^2 by Q0 (square-root and square-derivative fail);
  - replace tangent coefficient 1 by 0 (the tangent map and 1=0 fail);
  - increase the cleared exponent by 1 (jet identity and regression fail).
The original files were never changed for these mutation checks.

6. Assumptions and correspondence

No field, local ring, selected prime, ZMT principle, choice or classical
logic is required by the new theorem. All.seg has the usual univalence,
replacement and surjection parameters. There are no new axioms or
checker modifications. Reused proof files are relative symlinks;
shared and earlier proof files are untouched. Nothing is committed.

The development imports the direct flat/unramified theorem for its flat
variant. Its derivative-ideal proof uses a direct dual-number test;
it does not call DiagonalJacobian to obtain that witness.

Mathematics first, formalisation correspondence second:
  ../../doc/etale-monic-cover-analysis.tex (and the compiled PDF).
The note also discusses a separate, unformalised finite-cover argument.
Only its shortened local argument is implemented here.
