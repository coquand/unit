Local etale conclusion from one selected finite factor
====================================================

1. Checked statement

SelectedFlatLocal.Over[...].theorem
  (fd : Truncation.Trunc[SelectedData].carrier)

This has the SAME local base, prime, finite algebra, local ZMT,
presentation and flatness parameters as etale-flat-unramified/
FlatTheoremLocal. It replaces the global residue-field decomposition
by the following finite data:

  SelectedData = (e : B) * (x : B) * Not(q(j(e))) * Piece e x.

Piece e x consists of a coefficient list P over A and:
  PRoot: some N with s^N e P(x) in mE (after applying j);
  PSeparable: w in E and N with s^N e(P'(x)w-1) in mE;
  PGenerates: for EACH INDEX i of the fixed finite spanning family bs,
    a coefficient list C_i and N_i with
      s^(N_i) e (bs_i - C_i(x)) in mB.

The polynomial evaluations in E use j(x), j(e), j(s) and A->E.
The last identity is in B itself. All ideal memberships are explicit
finite IdealGenerated witnesses; the whole selected input is truncated.
There is no request for polynomial representations of every b in B,
no sum-one equation, and no collection of all residual factors.
Even idempotence of e is not needed by this local adapter: being outside
q and the displayed equations suffice.

The conclusion is the existing FlatLocalStatement.Conclusion:
merely t outside q and an actual localization T=E[1/t], with a standard
etale presentation and FormallyEtale.Etale T (the checked square-zero
lifting/uniqueness definition, together with finite presentation).

Other inputs remain explicit:
  A is a commutative set-ring with the existing local ideal m, its ideal
  laws, zero-or-unit decision and radical condition;
  q is a proper decidable prime predicate on E containing mE;
  A->B->E commutes, B is spanned over A by the nonempty finite list bs;
  j(s)-1 lies merely in mE;
  every z in E merely has a power of j(s) carrying it into j(B);
  E has a supplied finite presentation and is flat over A.
No global ZMT is invoked, and j:B->E need not be injective.

2. Exact private variants

FiniteIntroduction.seg is a private derived copy of the existing
etale-flat-unramified/Introduction.seg. Only Generates, Shift.generates',
and Main.Step0.Ci/e-gen were changed: they take i:Fin(suc n') and use
bs_i. All other mathematical proof text is unchanged.

FiniteFlatLocal.seg is a private derived copy of FlatLocal.seg. Its sole
proof change is using FiniteIntroduction instead of Introduction.
The polynomial loop, surjectivity, kernel generation, flatness transfer
and idempotent-kernel ending are unchanged.

private-variants.diff records these exact differences, including headers.
These are intentionally private source copies; the originals remain
untouched. The other dependencies are relative links.

SelectedFlatLocal.seg is derived from FlatTheoremLocal.seg. The search
through all factors, sum-one argument, FieldCase and FieldData were
removed. Selected[e,x,out,F] retains the refinement s'=s*e, the local
ZMT transport and the local theorem. It exposes theorem-of for actual
SelectedData and theorem for merely given SelectedData.

3. Denominator powers are retained

The refinement identity is reused from TheoremLocal.Refine:
  (s e)^(N+1) w = (s e^N) (s^N (e w)).
Both lift-E and the B-side generation step keep this exact exponent
and the original ideal witness. No injection from B/mB to a localized
special fibre is assumed. A field-theoretic construction must still
lift coefficients and clear powers of s to produce these witnesses.

4. Regression and mutations

SelectedLocalRegression runs the FULL new local theorem with
  A = E = F2, m=q=0,
  B = F2 x F2, j = first projection,
  bs = ((1,0),(0,1)), s=(1,0), selected e=1, x=0, P=X.

The two polynomial representations are C_0=1 and C_1=0. Their B-side
generation identities use N_i=1. The second vector is proved nonzero
in B and killed by j; its uncleared generation difference is also
proved nonzero. Thus this exercises both the noninjective map and an
indispensable denominator power, not just the trivial B=E case.

Two mutations in isolated temporary copies were rejected:
  replacing N+1 by N in lift-E;
  replacing the regression generation exponent 1 by 0.
Working files were never mutated.

5. Validation (31 October 2026)

  ./segc sag/etale-field-local-interface all

168 modules, 0 failed, 2.85 s.
Fresh built checker: 7704 declarations, 0 failed, 3.31 s.
The four owned modules contain 549 declarations, including 5 open
instructions. Every one of the 544 named declarations is covered by
etale-field-local-interface.opens and reports "nothing else opened".
They take at most 0.03 s each and open at most 28 separate definitions.

No new axioms, checker changes, shared-file changes or commits.
All.seg uses the existing univalence, replacement and surjection
parameters. The checking server is stopped.

6. Remaining obligations

This adapter does NOT prove SelectedData from unramifiedness. Producing
the selected primitive element, its separable polynomial and the finite
representations, then lifting coefficients and clearing denominators,
remains the field-to-local bridge.

It does not prove the former global residue-field decomposition or
an unconditional global theorem flat+unramified=>etale. It proves the
precise local implication once the displayed finite selected data are
supplied. The smaller interface removes the need to construct or retain
all factors merely to apply the local theorem.
