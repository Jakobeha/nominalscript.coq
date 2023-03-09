(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
From NS Require Import Misc.

(* Void-able type *)
Inductive vtype (type: Set): Set :=
| VVoid
| VType (a: type).
Arguments VVoid {type}.
Arguments VType {type} a.

(* Nominal (named) type *)
Inductive itype (type: Set): Set :=
| IType (name: string) (targs: list type).
Arguments IType {type} name targs.

(* Structural type *)
Inductive stype (type: Set): Set :=
| SFn (tparams: list string) (params: list type) (rparam: option type) (ret: vtype type)
| SArray (elem: type)
| STuple (elems: list type)
| SObject (fields: js_record type).
Arguments SFn {type} tparams params rparam ret.
Arguments SArray {type} elem.
Arguments STuple {type} elems.
Arguments SObject {type} fields.

(* Never-able type *)
Inductive ntype (type: Set): Set :=
| NNever
| NType (a: type).
Arguments NNever {type}.
Arguments NType {type} a.

(* Any-able, never-able, or nullable type *)
Inductive atype (type: Set): Set :=
| AAny
| AType (nullable: bool) (a: ntype type).
Arguments AAny {type}.
Arguments AType {type} nullable a.

(* Thin type: actual type that you write in nominalscript code *)
Inductive ttype': Set :=
| TTypeStructural (a: stype (atype ttype'))
| TTypeNominal (a: itype (atype ttype')).
Notation ttype := (atype ttype').
Notation vttype := (vtype ttype).
Notation ittype := (itype ttype).
Notation sttype := (stype ttype).
Notation nttype := (ntype ttype).

(* Fat type: resolved thin type (lookup supertypes and normalize), how the compiler sees thin types *)
Inductive ftype': Set :=
| FTypeStructural (s: stype (atype ftype'))
| FTypeNominal (id: itype (atype ftype')) (super_ids: list (itype (atype ftype'))) (s: option (stype (atype ftype'))).
Notation ftype := (atype ftype').
Notation vftype := (vtype ftype).
Notation iftype := (itype ftype).
Notation sftype := (stype ftype).
Notation nftype := (ntype ftype').
