# nominalscript.coq - Formalization of NominalScript's type system in Coq

nominalscript.coq defines `Inductive` definitions of NominalScript types, and `Inductive` definitions of a subset of its subtype relation.
It also embeds thin-type parsing via custom `Notation`.
Then, it defines and proves theorems about the subtype relation: reflexivity, symmetry, and transitivity.
It also defines a union and intersection relation from the subtype relation, and proves properties about those.

## Building / Installing

`opam install nominalscript`, or `opam install .` within this directory, should work.

If not, this follows the standard Coq package structure: run `./configure.sh` to generate a makefile, and then `make` to build the coq sources.

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

## Summary

- What I've accomplished:
  - In Coq, I defined the NominalScript type system and a large subset of the subtype relation, and proven reflexivity, anti-symmetry, and transitivity. I also created a small notation (custom expr) for thin types, defined union / intersection and proved properties on those based off of the subtype properties, and defined the subtype relation and properties as classes so that they can be generalized
  - In Rust, I wrote the code for the transpiler so that it compiles...however, right now it is still extremely buggy
- What I haven't accomplished:
  - In Coq, proven union + intersection distributivity (`a ⋃ (b ⋂ c) = (a ⋃ b) ⋂ (a ⋃ c)`) and intersection + union distributivity. These are probably hard due to how union and intersection are defined, and I'm not sure the additional subtype rule I need to create for them. Also, the subtype relation doesn't handle functions with different type parameters, as that requires substitution and introduces normalization and both are much harder to prove
  - In Rust, implemented additional tests (there is only one test for an example file which doesn't work) and fixed all of the bugs; I definitely didn't follow TDD writing this transpiler...
- Ideal future plans
  - In Coq, Prove subtyping for functions with different type parameters, prove union + intersection and intersection + union distributivity, and most of all, generalize so that it's very easy to formalize arbitrary type systems
  - In Rust, fix all of the bugs, implement tests, improve the documentation, refactor to make the code cleaner, write an LSP and tooling for NominalScript for true seamless integration onto any TypeScript project, and generalize so that it's very easy to add nominal type systems to arbitrary languages
