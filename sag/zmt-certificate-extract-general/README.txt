Generic degree-lowering certificate
===================================

Status: complete, checked, uncommitted. Five owned source files,253 owned
declarations. Existing sources/checker/shared files are unchanged relative
links. No new axioms, no choice, no field, CFN or Noetherianity hypothesis.

Exact shared input
------------------
GenericDegreeLoweringData.Over[R,setR,E,setE,iota,m,y,t,b].Data

R,E are arbitrary commutative set-rings, iota:R->E a ring map,
y:Fin m->E, b:Fin t->R. The record (constructor mkData) has fields:
 s          : E.R
 degree     : Base.Nat
 sT         : Ev.Polys
 homS       : X.Hom(pos degree)sT
 valueS     : Id E.R(Ev.deh sT)s
 a          : Fin m->Base.Nat
 q          : Fin m->Ev.Polys
 homQ i     : X.Hom(pos(a i))(q i)
 lower i    : Id E.R(E.mul s(P.power(y i)(suc(a i))))(Ev.deh(q i))
 congruence : FiniteIdeal.Over[E,t,iota b].Certificate s E.o.

Ev is exactly GenericDehomogenisation.Over[R,E,setR,iota,m,y].
X=CechPolynomialAction.Over[R,setR,suc m]. P=SectionsPowerAlgebra.Over[E].
Term lists use Fin(suc m)->Base.Nat exponents. The newest coordinate
inr tt is Z, evaluated at1; old coordinates inl i evaluate at y_i.
All degree bounds and powers use Base.Nat, finite ranks use Ring.Nat.
No structural equivalence with the fixed four-coordinate model is used.
Zero term lists and empty affine/ideal-generator lists are allowed.
The finite input degrees are natural as in the original ZMT4Certificate;
negative chart degrees are dealt with by the preceding section extraction,
not by requiring a negative natural exponent in this record.

Final theorem
-------------
GenericDegreeLoweringCertificate.Over[R,setR,E,setE,iota,m,y,t,b]
 .certificate(dat:GenericDegreeLoweringData.Over[same].Data)
  : ZMTCertificate.ZMTCert[R,E,iota,m,y,t,b].

The returned certificate has s=dat.s, its original congruence witness,
an explicit monic polynomial annihilating s, and one annihilating every
s*y_i. No finite module, stability statement or annihilator is an input.
.WithData[dat] exposes the complete construction:
 d = dat.degree + FiniteExponents.degree m dat.a;
 V = GenericFilteredSpan.Over[R,setR,E,setE,iota,m,y,d];
 reduction/reduced-span, actsS, actsY, IS and IY.

Proof and reusable constructions
--------------------------------
GenericDegreeBounds supplies complementary-summand bounds and a
constructive coordinate dichotomy. For every affine exponent beta, either
its total degree is<=sum_i a_i, or it explicitly factors as
 y^beta = y^v*y_i^(a_i+1),
 deg(beta)=deg(v)+a_i+1.
The recursion includes zero variables, arbitrary zero thresholds and all
coordinates; there is no hidden positive-rank assumption.

GenericFilteredSpan constructs ONE finite family from boxes(m,d):
 g_j=y^u for deg(u)<=d, and g_j=0 for the remaining box entries.
Its explicit coordinate representation Rep(x) is
 (alpha:Fin rank->R)*Id E.R x(sum_j g_j*iota(alpha_j)).
Every degree<=d monomial has an explicit index in this static box.
A term expands using a unit coefficient vector at that index; coordinate
vectors then add term by term. Thus no duplicate-counting or nodup axiom
is needed. Bounds, finite enumeration, coverage and1-in-the-span are all
constructed. No basis, linear independence, ring equivalence or quotient
module is asserted. Only generic exact combination lemmas from FibreSpan
are reused; its Finite predicate is not assumed or used.

For deg(beta)<=d+1, reduce s*y^beta:
 - In the small alternative, s=deh(sT) gives affine degree
   <=D+deg(beta)<=D+sum_i a_i=d.
 - In the large alternative, substitute the supplied lowering identity:
   y^v*deh(q_i) has degree<=deg(beta)-1<=d.
Polynomials are tracked by proved affine degree bounds; no artificial
homogenisation/padding is needed in the intermediate reductions.

For each generator g_j, this proves s*g_j lies in the same finite span.
Bumping its exponent at i proves (s*y_i)*g_j lies in that span too.
Zero box generators are handled by explicit zero coordinates. The common
finite family contains1, so the unchanged DeterminantTrick.Integral and
CharacteristicMonic.CharMonic give explicit monic annihilators. All these
matrices and faithful vectors are built from the coordinate representations.

Source/import order
-------------------
 GenericDegreeLoweringData        29 declarations
 GenericDegreeBounds             47
 GenericFilteredSpan             61
 GenericDegreeLoweringCertificate62
 GenericDegreeLoweringRegression54
 Total                          253
The mathematical sources depend only on existing generic exponent/action,
dehalgebra, finite box/list lookup, generic monomial coordinate lemmas,
FibreSpan combination laws, determinant trick and characteristic monic
machinery, plus generic natural arithmetic/dichotomy. The larger unchanged
All.seg baseline is copied from the completed assembly development.

Regressions and scope
---------------------
Constructed input data/certificates over Z with m=0 and m=4 affine
generators y_i=0. Both small and large coordinate-reduction outputs are
checked for arbitrary variable indices. Over Z/4, m=4, y_i=2 and b=2,
all y_i are genuinely nonzero; a_i=1 and q_i=0 use nilpotence 2^2=0.
No finiteness/stability data are supplied in these examples.
A deliberate mutation replacing d=D+sum a by d=D is rejected in the
small reduction bound, restored, and both final modules check again.

This is the final algebraic certificate step; it does not redo section
construction, Rees comparison or arbitrary-base descent. It works in all
finite affine ranks, so no separate small-rank certificate theorem is
required. See VALIDATION.txt and zmt-certificate-extract-general.opens.
The .opens file records the measured unfolding inventory of every owned
declaration, not an independently minimal allowlist.
