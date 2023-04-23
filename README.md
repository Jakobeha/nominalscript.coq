# nominalscript.coq - Formalization of NominalScript's type system in Coq

nominalscript.coq defines `Inductive` definitions of NominalScript types, and `Inductive` definitions of a subset of its subtype relation.
It also embeds thin-type parsing via custom `Notation`.
Then, it defines and proves theorems about the subtype relation: reflexivity, symmetry, and transitivity.
It also defines a union and intersection relation from the subtype relation, and proves properties about those.

## Building / Installing

`opam install nominalscript`, or `opam install .` within this directory, should work.

If not, this follows the standard Coq package structure: run `./configure.sh` to generate a makefile from `_CoqProject`, and then `make` to build the coq sources.

## Project Structure

- `NS/`: Where the source (coq) is located
  - `Misc.v`: Utility definitions, theorems, and tactics
  - `HigherOrder.v`: `Forall` typeclass which is useful for higher-order inductives (this could honestly go in `Misc.v` since it's the only definition here)
  - `JsRecord.v`: Definitions, theorems, and tactics for a "map" or "javascript record" represented by a list of `string * A` pairs
  - `TypesBase.v`: Defines nominalscript types
  - `TypesSimpleHelpers.v`: Helper definitions and lemmas for the nominalscript types
  - `TypesNotation.v`: Defines a notation for thin types
  - `TypesSubtype.v`: Defines the general subtype relation and properties, subtype relations for each sub-structure in the nominalscript types, and proves the subtype properties on nominalscript fat types

The key file is probably `TypesSubtype.v`, because this is where we prove the important lemmas.
