SAG Section 7.1, worker B: kernels, quotient modules and cokernels
==================================================================

Checked: Lemma 7.1.6 (kernels) and Proposition 7.1.13 (cokernels) for
weakly quasi-coherent modules, from Loc, SQC and Z-choice.  No new axiom,
no checker change.  Other directories are linked read-only.

Files
-----
Submodules       linear maps; submodules (proposition-valued, closed under
                 the operations) and their elements as a module; kernel
                 and image of a linear map; f onto its image.
QuotientModule   P / K for a submodule K: the effective quotient of P by
                 "b - a in K", operations descended along the projection.
                 The projection is linear, surjective, with kernel K.
PointQC          7.1.5 at a scalar r (sections over D(r) are m / r^N; m
                 vanishing on D(r) is killed by a power of r), and its
                 equivalence with Modules.WeaklyQC.
Kernel716        7.1.6.  No localised module is used: a section of the
                 kernel is m / r^N with m in P; r^K f(m) = 0, so it is
                 (r^K m) / r^(K+N) with r^K m in the kernel.
UnitAffine       D(r) is Spec R[1/r], with R[1/r] finitely presented.
Surjection       If p : P -> Q is linear and onto, with kernel K, and P and K
                 are weakly quasi-coherent, then so is Q.  A section of Q
                 over D(r) lifts to P because its preimages form a K-torsor
                 over the affine D(r) (Theorem 7.3.6, qc-schemes/
                 AffineVanishing).
Cokernel7113     7.1.13: Surjection for M -> f(M) (kernel ker f, 7.1.6)
                 and for N -> N / f(M) (kernel f(M)).  The paper's reduction
                 through embeddings and M / ker f is not needed, nor the long
                 exact sequence 7.3.4.
CokernelExamples P / P has one element; P / 0 -> P is injective; one negative
                 test.

The localised module M_r
Localisation     M_r as a set: pairs (m, p) = m / r^p, divided by
                 "r^K (r^q m - r^p m') = 0 for some K".  The canonical map
                 phi : M_r -> M^D(r).  FromQC / ToQC: phi is an equivalence
                 iff the two PointQC clauses hold at r, i.e. our clauses are
                 the paper's Definition 7.1.5.
LocalisationModule  the module operations on M_r, their laws, and
                 linearity of phi.
Localisation712  7.1.2 as stated: for a scheme X, M(X) is a module over
                 X -> R and psi : M(X)_f -> prod_x (M x)_(f x) is a linear
                 equivalence (injective by scheme boundedness, surjective by
                 qc-schemes/FractionSections).  Restrict.theorem: 7.1.8 for
                 U = X, M(X)_f = M(D(f)), for weakly quasi-coherent fibres;
                 Open[...].theorem: the same for any open U (a scheme).
LocalisationExamples  M_0 = 0; one negative test.
ModuleSIP        structure identity: a linear bijection A ~ B gives A = B
                 in the type of modules (record eliminator for eta, then
                 induction on equivalences; laws are propositions).
LocalisationEq   7.1.2 and 7.1.8 (any open U) as equalities of modules over
                 X -> R.

Main statements
---------------
Cokernel7113[l].Over[R,setR,axioms].At[M,N,f,wM,wN].theorem
  : Modules.WeaklyQC (N / f(M))
Cokernel7113[l].Over[R,setR,axioms].kernel M N f wM wN
  : Modules.WeaklyQC (ker f)
where wM : Modules.WeaklyQC M, wN : Modules.WeaklyQC N.

Not done here: the general map M (x) A -> M^Spec(A) of Remark 7.1.3 (it
needs the tensor product of modules); only its case M_r -> M^D(r) is used
in the paper, and that is phi.

Check: direct seg on All.seg (Sections 2-5, torsor/, bridge7/, all of qc-schemes/
including 7.1.9-7.1.12, and this directory): all of Section 7.1.
