SAG Section 7.1 bridge and Theorem 7.3.6 from the SAG axioms
============================================================

Worker B's development. Check from the repository root:
  ./segc sag/bridge7 all
Independent check:  (cd sag/bridge7 && "$(cabal list-bin exe:seg)" All.seg)

All.seg loads Sections 2-5 (through ../schemes, ../gluing) and the
torsor/ files needed for 7.3.5-7.3.6 together; they share the same
foundation files.  Everything else is a read-only symlink; torsor/ is
not modified.  The shared interface is ../SEC7-INTERFACE.md.

NatFin.seg      Sections 2-5 and torsor/ use different Nat and Fin
                (Fin (n+1) = Fin n + Top, resp. Opt (Fin n)).
                toN, toF and their inverses.
RingBridge.seg  ring R : Alg73.CRing.  Units are the same type; powers
                (power) and finite sums (sum) agree along toN, toF;
                Locality gives torsor's LocR (loc).
Modules.seg     Module = Alg73.Mod[ring R]; regular; pi X Mx = M(X) (7.1.1).
                Fractions: Kills g x K (g^K x = 0, K in Ring's Nat; upwards
                closed), Same (equal fractions), value (x/g^N on D(g)).
                WeaklyQC (7.1.5), WqcBundle (7.1.7), Restriction X Mx
                (7.1.8 for U = X, the form torsor's 7.3.6 assumes).
ZBridge.seg     torsor's ZChoice for X = Spec A, A finitely presented,
                from SAGAxioms.ZChoice: the functions are x |-> x(f_i);
                hom-sum carries sum r_i f_i = 1 to every point.
Theorem736.seg  Torsors[X,Mx,wq,T,ts]: on an affine X every M-torsor T
                merely has a section, from Loc, SQC, Z-choice and
                wq : Restriction X Mx (presented, affine, small-affine).

Still a hypothesis: wq.  It becomes a theorem when worker A's 7.1.8
gives Restriction X Mx from WqcBundle X Mx.
