(* -*- company-coq-local-symbols: (("U" . ?∪) ("I" . ?∩) ("==" . ?≡) ("><" . ?≷)); -*- *)
(* Add LoadPath should not be necessary but it is *)
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FinFun.
Require Import Coq.Program.Equality.
From NS Require Import Misc.
From NS Require Import TypesBase.
From NS Require Import TypesNotation.
From NS Require Import TypesSimpleHelpers.

Set Default Timeout 10.

Create HintDb hints.

Inductive Zip (A: Set)       := Zip_ (_: list A).
Arguments Zip_ {A} _%list_scope.
Inductive JsrZip (A: Set)    := JsrZip_ (_: js_record A).
Arguments JsrZip_ {A} _.
Inductive Intersect (A: Set) := Intersect_ (_: list A).
Arguments Intersect_ {A} _%list_scope.

Axiom Zip_inj : Injective Zip.
Axiom JsrZip_inj : Injective JsrZip.
Axiom Intersect_inj : Injective Intersect.
Ltac injections :=
  repeat lazymatch goal with
  | H : Zip ?a = Zip ?b |- _ => apply Zip_inj in H
  | H : JsrZip ?a = JsrZip ?b |- _ => apply JsrZip_inj in H
  | H : Intersect ?a = Intersect ?b |- _ => apply Intersect_inj in H
  end.

Inductive relation_type : Set :=
| ftype_relation_type
| itype_relation_type (_: relation_type)
| stype_relation_type (_: relation_type)
| otype_relation_type (_: relation_type)
| vtype_relation_type (_: relation_type)
| tparam_relation_type (_: relation_type)
| variance_relation_type
| option_relation_type (_: relation_type)
| Zip_relation_type (_: relation_type)
| JsrZip_relation_type (_: relation_type)
| Intersect_relation_type (_: relation_type)
.

Fixpoint rt_type (r: relation_type): Set :=
match r with
| ftype_relation_type => ftype
| itype_relation_type r => itype (rt_type r)
| stype_relation_type r => stype (rt_type r)
| otype_relation_type r => otype (rt_type r)
| vtype_relation_type r => vtype (rt_type r)
| tparam_relation_type r => tparam (rt_type r)
| variance_relation_type => variance
| option_relation_type r => option (rt_type r)
| Zip_relation_type r => Zip (rt_type r)
| JsrZip_relation_type r => JsrZip (rt_type r)
| Intersect_relation_type r => Intersect (rt_type r)
end.

Inductive variance : Set :=
| Invariant
| Covariant
| Contravariant
| Bivariant
.

Reserved Notation "x >= y" (at level 70, no associativity).
Reserved Notation "x <= y" (at level 70, no associativity).
Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x >< y" (at level 70, no associativity).

(* Unification relation: defines the entire type lattice, includine
   subtype, supertype, union, intersection, top, and bottom *)
Inductive IsSubtype : forall {A: Set}, A -> A -> Prop :=
| IS_Any : forall x, x <= FAny
| IS_Never : forall x, FNEVER <= x
| IS_Null : forall x, IsNullable x -> FNULL <= x
where "x <= y" := (IsSubtype x y)
  and "x >= y" := (IsSubtype y x).
