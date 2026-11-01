Coefficient spectrum data (2026-11-01)
====================================

This root reuses the Eilenberg-MacLane construction in ../em through
relative links. EMSpectrum is the only new theorem file. All.seg imports
only the required prefix of the em development.

For an abelian group M, EMSpectrum.Coefficient constructs:
  space 0 = M;
  space (n+1) = K(M,n+1);
  pointed equivalences Omega(space(n+1)) ~ space n.
The first structure equivalence preserves the given addition on M.
The parameters are only Theory's existing univ, images, surjections.

This is a coefficient object described by Omega-spectrum data. It is
NOT a construction of the category of spectra, its mapping types,
finite semi-Segal data, copowers, stability, or ordinary homology.
The model work still needs all those constructions and their comparison.
See ../../doc/hcat-segal-homology.pdf for the intended interpretation.
Follow ../hcat/HANDOFF.md and ../../../seg/WRITING.md (at the repository
root: seg/WRITING.md) for writing discipline; do not edit linked sources.

Checks from unit/:
  ./segc sag/hcat-spectrum changed
  ./segc sag/hcat-spectrum all
  ./segc sag/hcat-spectrum stop
36 modules; 1001 declarations; 0 failures. Fresh --opened: 0.14 s.
Every module is under 1 s. The checking server is stopped at handoff.
