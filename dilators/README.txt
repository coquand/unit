Dilators, constructively (Girard, Proof Theory and Logical Complexity, ch. 8-9)
================================================================================

dilator.seg   pre-dilators on the category of finite ordinals with strictly
              increasing maps (written as words over {o, i}); the normal form
              theorem (least supports, the trace); denotations at a decidable
              linear order and their order; well-foundedness by accessibility
              for Id, 1, D + E, D . E and the polynomial dilators; 2^X and the
              pre-dilator 2^D, up to epsilon_0 and the Howard ordinal;
              morphisms, connected components (9.1.5-9.1.7) and kinds
              (9.1.10-9.1.11).
ordinal.seg   Wainer: the slow growing hierarchy collapses the Hardy hierarchy
              one level down (function extensionality as a module parameter,
              for the last statement only).

The note doc/dilators-constructive.pdf follows these files.

Check from the repository root:
  (cd dilators && "$(cabal list-bin exe:seg)" dilator.seg)   1344 declarations
  (cd dilators && "$(cabal list-bin exe:seg)" ordinal.seg)     51 declarations
