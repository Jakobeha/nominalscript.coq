(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
From NS Require Import Misc.

(* Return (void-able) type *)
Inductive vtype (type: Set): Set :=
| VVoid
| V (a: type).
Arguments VVoid {type}.
Arguments V {type} a.

(* Nominal (identifer) type *)
Inductive itype (type: Set): Set :=
| I (name: string) (targs: list type).
Arguments I {type} name targs.

Inductive variance: Set :=
| Invariant
| Covariant
| Contravariant
| Bivariant.

(* Type parameter *)
Inductive tparam (type: Set): Set :=
| TParam (v: variance) (name: string) (supers: list type).
Arguments TParam {type} v name supers.

(* Optional (different than nullable) type *)
Inductive otype (type: Set): Set :=
| O (optional: bool) (a: type).
Arguments O {type} optional a.


(* Structural type *)
Inductive stype (type: Set): Set :=
| SFn (tparams: list (tparam type)) (thisp: type) (params: list (otype type)) (rparam: type) (ret: vtype type)
| SArray (elem: type)
| STuple (elems: list (otype type))
| SObject (fields: js_record (otype type)).
Arguments SFn {type} tparams thisp params rparam ret.
Arguments SArray {type} elem.
Arguments STuple {type} elems.
Arguments SObject {type} fields.

(* Thin type: actual type that you write in nominalscript code *)
Inductive ttype: Set :=
| TAny
| TNever (nullable: bool)
| TStructural (nullable: bool) (structure: stype ttype)
| TNominal (nullable: bool) (id: itype ttype).
Notation vttype := (vtype ttype).
Notation ittype := (itype ttype).
Notation ttparam := (tparam ttype).
Notation ottype := (otype ttype).
Notation sttype := (stype ttype).

(* Fat type: resolved thin type (lookup supevtypes and normalize), how the compiler sees thin types *)
Inductive ftype: Set :=
| FAny
| FNever (nullable: bool)
| FStructural (nullable: bool) (structure: stype ftype)
| FNominal (nullable: bool) (id: itype ftype) (sids: list (itype ftype)) (structure: option (stype ftype)).
Notation vftype := (vtype ftype).
Notation iftype := (itype ftype).
Notation ftparam := (tparam ftype).
Notation oftype := (otype ftype).
Notation sftype := (stype ftype).

Definition TEMPTY: ttype := TStructural false (STuple nil).
Definition FEMPTY: ftype := FStructural false (STuple nil).
