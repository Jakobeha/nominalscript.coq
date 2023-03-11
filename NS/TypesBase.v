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
| Vt (a: type).
Arguments VVoid {type}.
Arguments Vt {type} a.

(* Nominal (identifer) type *)
Inductive itype (type: Set): Set :=
| It (name: string) (targs: list type).
Arguments It {type} name targs.

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
| Ot (optional: bool) (a: type).
Arguments Ot {type} optional a.


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

Inductive IType_Forall {type: Set} (P: type -> Prop): itype type -> Prop :=
| Forall_It : forall name targs, List.Forall P targs -> IType_Forall P (It name targs).
Inductive VType_Forall {type: Set} (P: type -> Prop): vtype type -> Prop :=
| Forall_VVoid : VType_Forall P VVoid
| Forall_Vt : forall x, P x -> VType_Forall P (Vt x).
Inductive OType_Forall {type: Set} (P: type -> Prop): otype type -> Prop :=
| Forall_Ot : forall optional x, P x -> OType_Forall P (Ot optional x).
Inductive TParam_Forall {type: Set} (P: type -> Prop): tparam type -> Prop :=
| Forall_TParam : forall variance name supers, List.Forall P supers -> TParam_Forall P (TParam variance name supers).
Inductive SType_Forall {type: Set} (P: type -> Prop): stype type -> Prop :=
| Forall_SFn : forall tparams thisp params rparam ret,
    List.Forall (TParam_Forall P) tparams -> P thisp -> List.Forall (OType_Forall P) params -> P rparam -> VType_Forall P ret ->
    SType_Forall P (SFn tparams thisp params rparam ret)
| Forall_SArray : forall elem, P elem -> SType_Forall P (SArray elem)
| Forall_STuple : forall elems, List.Forall (OType_Forall P) elems -> SType_Forall P (STuple elems)
| Forall_SObject : forall fields, List.Forall (OType_Forall P << snd) fields -> SType_Forall P (SObject fields).

Axiom ttype_rec':
  forall (P: ttype -> Prop)
    (fAny: P TAny)
    (fNever: forall nullable, P (TNever nullable))
    (fStructural: forall nullable structure, SType_Forall P structure -> P (TStructural nullable structure))
    (fNominal: forall nullable id, IType_Forall P id -> P (TNominal nullable id))
    (x: ttype), P x.
Axiom ftype_rec':
  forall (P: ftype -> Prop)
    (fAny: P FAny)
    (fNever: forall nullable, P (FNever nullable))
    (fStructural: forall nullable structure, SType_Forall P structure -> P (FStructural nullable structure))
    (fNominal: forall nullable id sids structure, IType_Forall P id -> List.Forall (IType_Forall P) sids -> Option_Forall (SType_Forall P) structure -> P (FNominal nullable id sids structure))
    (x: ftype), P x.

Definition TNEVER: ttype := TNever false.
Definition TNULL : ttype := TNever true.
Definition TEMPTY: ttype := TStructural false (STuple nil).
Definition FNEVER: ftype := FNever false.
Definition FNULL : ftype := FNever true.
Definition FEMPTY: ftype := FStructural false (STuple nil).
