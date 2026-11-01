# Module scope and import identity in Unit

Independent mathematical developments should compose without renaming
their internal modules or arranging imports in a special order. The
combination of `sag/categories` and `sag/presentations` exposed two
different name-resolution problems. They need separate solutions:
lexical scope for module declarations, and qualified imports with
identity-preserving aliases.

This is a proposed language change. No resolver, loader or checker change
has been made for it.

## The observed clashes

`PresentedAlgebra` and `PresentationExistence` have internal modules named
`Descent`. The category development also imports a file `Descent.seg`.
Their qualified names differ, but the resolver rejects an internal module
whose short name is already visible. Importing the presentation files
before the category file avoids the clash.

`CompletionUP.Instance.Universal` similarly clashed with the imported
polynomial file `Universal.seg`. The internal module was renamed to
`ForEvery` to combine the developments.

There are also two distinct files named `Equivalences.seg`, in
`sag/categories` and `sag/presentations`, with overlapping member names and
different signatures. They cannot currently be imported together by
qualification. In particular, the existing `PresentationComparison`
dependency expects the presentation version's `injective` lemma.

These are clashes of names and library boundaries. They do not identify
different mathematical notions, and their workarounds should not appear
in mathematical exposition.

## Current implementation

The relevant implementation is in `src/SegParse.hs` and `app/Main.hs`.

In the resolver, `fresh` consults the whole visible scope using `look`.
It permits names exposed by `open` or record-field opening to be hidden,
but rejects other already-visible names. `resUnits` calls this check for
new modules and module instances. Consequently it does not distinguish
an enclosing module name from a declaration in the current module body.

The variable and level no-shadowing check is a separate mechanism,
`shadowReport`. Its source comment explicitly distinguishes variables
and levels, whose names are used in dependencies, from modules and
definitions reached by qualified names or resolved identities.

In the loader, `expand` handles `import F` by reading `F.seg` relative to
the entry point's import directory, recursively expanding its imports,
and wrapping its declarations as `module F { ... }`. Its `seen` set is
indexed by the string `F`. Thus the same basename serves as the file
locator, local module name and import deduplication key. The grammar has
neither a qualified source path nor an import alias.

## First change to consider

Permit a module declaration or module alias to shadow a module from an
enclosing lexical scope. Continue rejecting two declarations of the same
name in the same scope. Keep the current restrictions on variables and
levels; their role in dependency handling requires separate reasoning.

For example, an imported `Descent` and a local
`PresentedAlgebra.Over.Descent` should be allowed to coexist. Unqualified
lookup inside the latter's scope should follow the lexical binding; an
explicit module alias established before that binding can retain access
to the outer module when necessary. Already-resolved references must keep
their original identities.

This requires the resolver to distinguish the current lexical frame from
the enclosing scope. Broadly weakening `fresh` without making that
distinction could admit duplicate declarations in one scope.

The intended change adds programs that are currently rejected. It must
not change the resolution or meaning of previously accepted programs.

## Qualified imports and aliases

A second change should distinguish a source's location from its local
name. Possible syntax, not yet implemented, is:

```text
import "sag/categories/Equivalences.seg" as CatEquiv;
import "sag/presentations/Equivalences.seg" as PresEquiv;
```

The syntax is less important than the identity rule: an alias names an
existing imported module instance. It must not create a new copy of its
definitions or nominal record types. Importing the same instance under
two aliases must preserve record identity without requiring an
isomorphism or a transport.

Conversely, distinct source files with the same basename must remain
distinct. A basename alone cannot be the import registry key.

The source identity must account for the symlinks used throughout the
repository. Instantiation context also matters: imports occur inside
parameterised theory segments, and a shared source does not justify
identifying different parameter instances. The design must distinguish
source identity, the resolved module instance and the name bound to that
instance in a client.

Dependency bindings must be preserved as well. A source using
`Equivalences.injective` must continue to refer to its intended dependency
when a client calls that source `Comparison` or imports another
`Equivalences`. Merely wrapping the current textual expansion in an
alternative module name does not establish this property. The design
must specify how a module's dependencies are resolved, including the
case where those dependencies have previously been supplied by an
entry-point import list rather than declared in the source itself.

Changing dependency resolution must not silently reinterpret existing
unqualified imports. A compatibility rule for the current entry-point
style should be specified before implementation.

## Regression cases

The lexical-scope change should cover an imported module and an unrelated
internal module with the same short name, continued rejection of
duplicates in one scope, preservation of earlier references, and continued
rejection of prohibited variable or level shadowing. The actual `Descent`
and `Universal` clashes provide application regressions.

Qualified imports should cover two distinct same-basename files, two
aliases for the same module instance, symlinked dependencies, nominal
records shared across aliases, parameterised imports, and preservation of
the imported source's dependency bindings. Explicit qualified imports
must not depend on the order of unrelated client imports.

No kernel equality or conversion rule needs to change to address these
name-resolution problems. Changes should remain in loading and
elaboration, with resolved terms retaining their existing identities.

## Work order

First isolate the lexical-scope problem with small examples and implement
the current-frame freshness rule. Then specify import identity and
dependency resolution before adding qualified imports. Implement and
check the alias mechanism against nominal-record identity before using
it to combine the two `Equivalences` libraries.

The existing passing mathematical developments should remain stable
checkpoints. Resolve the language issue in a separate change; do not
undertake a library-wide naming migration as a substitute.
