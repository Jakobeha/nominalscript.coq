(* Add LoadPath should not be necessary but it is *)
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
From Equations Require Import Equations.
From NS Require Import Misc.
From NS Require Import HigherOrder.
From NS Require Import JsRecord.

(* Return (void-able) type *)
Inductive vtype (A: Set): Set :=
| VVoid
| Vt (a: A).
Arguments VVoid {A}.
Arguments Vt {A} a.

(* Nominal (identifer) A *)
Inductive itype (A: Set): Set :=
| It (name: string) (targs: list A).
Arguments It {A} name targs.

Inductive variance: Set :=
| Invariant
| Covariant
| Contravariant
| Bivariant.

(* A parameter *)
Inductive tparam (A: Set): Set :=
| TParam (v: variance) (name: string) (supers: list A).
Arguments TParam {A} v name supers.

(* Optional (different than nullable) A *)
Inductive otype (A: Set): Set :=
| Ot (optional: bool) (a: A).
Arguments Ot {A} optional a.


(* Structural A *)
Inductive stype (A: Set): Set :=
| SFn (tparams: list (tparam A)) (thisp: A) (params: list (otype A)) (rparam: A) (ret: vtype A)
| SArray (elem: A)
| STuple (elems: list (otype A))
| SObject (fields: js_record (otype A)).
Arguments SFn {A} tparams thisp params rparam ret.
Arguments SArray {A} elem.
Arguments STuple {A} elems.
Arguments SObject {A} fields.

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
Derive NoConfusion for ftype.
Derive Subterm for ftype.
Notation vftype := (vtype ftype).
Notation iftype := (itype ftype).
Notation ftparam := (tparam ftype).
Notation oftype := (otype ftype).
Notation sftype := (stype ftype).

(* Equivalent definition of ftype which has depth for proper recursion *)
Inductive option' (A: nat -> Set): nat -> Set :=
| Some': forall {n: nat}, A n -> option' A n
| None': option' A 0.
Arguments Some' {A n}.
Arguments None' {A}.
Inductive list' (A: nat -> Set): nat -> Set :=
| Nil': list' A 0
| Cons': forall {n n0: nat}, A n -> list' A n0 -> list' A (max n n0).
Arguments Nil' {A}.
Arguments Cons' {A n n0} a l.

Inductive IType_Forall {A: Set} (P: A -> Prop): itype A -> Prop :=
| Forall_It : forall name targs, List.Forall P targs -> IType_Forall P (It name targs)
. Global Instance Forall_itype: Forall itype := @IType_Forall.
Inductive VType_Forall {A: Set} (P: A -> Prop): vtype A -> Prop :=
| Forall_VVoid : VType_Forall P VVoid
| Forall_Vt : forall x, P x -> VType_Forall P (Vt x)
. Global Instance Forall_vtype: Forall vtype := @VType_Forall.
Inductive OType_Forall {A: Set} (P: A -> Prop): otype A -> Prop :=
| Forall_Ot : forall optional x, P x -> OType_Forall P (Ot optional x)
. Global Instance Forall_otype: Forall otype := @OType_Forall.
Inductive TParam_Forall {A: Set} (P: A -> Prop): tparam A -> Prop :=
| Forall_TParam : forall variance name supers, List.Forall P supers -> TParam_Forall P (TParam variance name supers)
. Global Instance Forall_tparam: Forall tparam := @TParam_Forall.
Inductive SType_Forall {A: Set} (P: A -> Prop): stype A -> Prop :=
| Forall_SFn : forall tparams thisp params rparam ret,
    List.Forall (TParam_Forall P) tparams -> P thisp -> List.Forall (OType_Forall P) params -> P rparam -> VType_Forall P ret ->
    SType_Forall P (SFn tparams thisp params rparam ret)
| Forall_SArray : forall elem, P elem -> SType_Forall P (SArray elem)
| Forall_STuple : forall elems, List.Forall (OType_Forall P) elems -> SType_Forall P (STuple elems)
| Forall_SObject : forall fields, JsRecordForall (OType_Forall P) fields -> SType_Forall P (SObject fields)
. Global Instance Forall_stype: Forall stype := @SType_Forall.
Inductive SType_Forall' {A: Set} (P: A -> Prop): stype A -> Prop :=
| Forall'_SFn : forall tparams thisp params rparam ret,
    List.Forall (TParam_Forall P) tparams -> P thisp -> List.Forall (OType_Forall P) params -> P rparam -> VType_Forall P ret ->
    SType_Forall' P (SFn tparams thisp params rparam ret)
| Forall'_SArray : forall elem, P elem -> SType_Forall' P (SArray elem)
| Forall'_STuple : forall elems, List.Forall (OType_Forall P) elems -> SType_Forall' P (STuple elems)
| Forall'_SObject : forall fields, JsRecordNoDupForall (OType_Forall P) fields -> SType_Forall' P (SObject fields)
.

Axiom ttype_ind':
  forall (P: ttype -> Prop)
    (fAny: P TAny)
    (fNever: forall nullable, P (TNever nullable))
    (fStructural: forall nullable structure, SType_Forall P structure -> P (TStructural nullable structure))
    (fNominal: forall nullable id, IType_Forall P id -> P (TNominal nullable id))
    (x: ttype), P x.
Axiom ttype_ind'0:
  forall (P: ttype -> Prop)
    (fAny: P TAny)
    (fNever: forall nullable, P (TNever nullable))
    (fStructural: forall nullable structure, SType_Forall' P structure -> P (TStructural nullable structure))
    (fNominal: forall nullable id, IType_Forall P id -> P (TNominal nullable id))
    (x: ttype), P x.
Axiom ftype_ind':
  forall (P: ftype -> Prop)
    (fAny: P FAny)
    (fNever: forall nullable, P (FNever nullable))
    (fStructural: forall nullable structure, SType_Forall P structure -> P (FStructural nullable structure))
    (fNominal: forall nullable id sids structure, IType_Forall P id -> List.Forall (IType_Forall P) sids -> Option_Forall (SType_Forall P) structure -> P (FNominal nullable id sids structure))
    (x: ftype), P x.
Axiom ftype_ind'0:
  forall (P: ftype -> Prop)
    (fAny: P FAny)
    (fNever: forall nullable, P (FNever nullable))
    (fStructural: forall nullable structure, SType_Forall' P structure -> P (FStructural nullable structure))
    (fNominal: forall nullable id sids structure, IType_Forall P id -> List.Forall (IType_Forall P) sids -> Option_Forall (SType_Forall' P) structure -> P (FNominal nullable id sids structure))
    (x: ftype), P x.

Definition TNEVER: ttype := TNever false.
Definition TNULL : ttype := TNever true.
Definition TEMPTY: ttype := TStructural false (STuple nil).
Definition FNEVER: ftype := FNever false.
Definition FNULL : ftype := FNever true.
Definition FEMPTY: ftype := FStructural false (STuple nil).
