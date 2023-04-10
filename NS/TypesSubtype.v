(* -*- company-coq-local-symbols: (("U" . ?∪) ("I" . ?∩)); -*- *)
(* Add LoadPath should not be necessary but it is *)
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Lia.
From NS Require Import Misc.
From NS Require Import JsRecord.
From NS Require Import TypesBase.
From NS Require Import TypesNotation.
From NS Require Import TypesSimpleHelpers.

Set Default Timeout 10.

Local Open Scope list_scope.
Local Notation "a <= b" := (Bool.le a b) : bool_scope.
Local Notation "a >= b" := (Bool.le b a) : bool_scope.

(* Subtype relation *)
Class Subtype (A: Set) := subtype: relation A.
(* Definition wrapper prevents Coq from printing everything as a subtype relation
   while still printing explicitly defined subtype relations *)
Definition ap_Subtype {A: Set} (S: Subtype A) (lhs rhs: A) := S lhs rhs.
Notation "'[' subtype ']' lhs '<:' rhs" := (ap_Subtype subtype lhs rhs) (at level 60, lhs at next level, rhs at next level, no associativity).
Notation "'[' subtype ']' lhs ':>' rhs" := (ap_Subtype subtype rhs lhs) (at level 60, lhs at next level, rhs at next level, no associativity, only parsing).
Notation "lhs '<:' rhs" := (subtype lhs rhs) (at level 60, rhs at next level, no associativity).
Notation "lhs ':>' rhs" := (subtype rhs lhs) (at level 60, rhs at next level, no associativity, only parsing).

(* From subtype relation *)
Inductive HasVariance {A: Set} {S: Subtype A} (lhs: A) (rhs: A): variance -> Prop :=
| IsBivariant     : lhs <: rhs \/ lhs :> rhs -> HasVariance lhs rhs Bivariant
| IsCovariant     : lhs <: rhs              -> HasVariance lhs rhs Covariant
| IsContravariant :              lhs :> rhs -> HasVariance lhs rhs Contravariant
| IsInvariant     : lhs <: rhs -> lhs :> rhs -> HasVariance lhs rhs Invariant
.

Definition IsBounded {A: Set} {S: Subtype A} (x min max: A): Prop := min <: x /\ x <: max.
Notation "min '<:' x '<:' max" := (IsBounded x min max) (at level 64, no associativity).

Definition Union {A: Set} {S: Subtype A} (lhs rhs uni: A): Prop := uni <: lhs /\ uni <: rhs /\ forall a, a <: lhs -> a <: rhs -> a <: uni.
Notation "'(U)'" := Union.
Notation "lhs 'U' rhs '=' a" := (Union lhs rhs a) (at level 60, rhs at next level, no associativity).

Definition Intersection {A: Set} {S: Subtype A} (lhs rhs int: A): Prop := lhs <: int /\ rhs <: int /\ forall a, a <: int -> a <: lhs /\ a <: rhs.
Notation "'(I)'" := Intersection.
Notation "lhs 'I' rhs '=' a" := (Intersection lhs rhs a) (at level 60, rhs at next level, no associativity).

Class EqvType (A: Set) := eqv_type: relation A.
Definition ap_EqvType {A: Set} (S: EqvType A) (lhs rhs: A) := S lhs rhs.
Notation "'[' eqv_type ']' lhs '==' rhs" := (ap_EqvType eqv_type lhs rhs) (at level 60, lhs at next level, rhs at next level, no associativity).
Notation "lhs '==' rhs" := (eqv_type lhs rhs) (at level 60, rhs at next level, no associativity).

Class IsValidType (A: Set) := is_valid_type: A -> Prop.
Definition IsValidType_always {A: Set}: IsValidType A := fun _ => True.

(* Subtype properties *)
Unset Implicit Arguments.
Class Top (A: Set): Set := top: A.
Class Bottom (A: Set): Set := bottom: A.
Class SubtypeTop (A: Set) `{_Subtype: Subtype A} `{_Top: Top A}: Prop := subtype_top: forall (a: A), a <: top.
Class SubtypeBottom (A: Set) `{_Subtype: Subtype A} `{_Bottom: Bottom A}: Prop := subtype_bottom: forall (a: A), bottom <: a.
Class SubtypeRefl (A: Set) `{_Subtype: Subtype A} `{_IsValidType: IsValidType A}: Prop := subtype_refl: forall (a: A), is_valid_type a -> a <: a.
Class SubtypeAntisym (A: Set) `{_Subtype: Subtype A} `{_EqvType: EqvType A}: Prop := subtype_antisym: forall (a b: A), a <: b -> b <: a -> a == b.
Class SubtypeTrans (A: Set) `{_Subtype: Subtype A}: Prop := subtype_trans: forall (a b c: A), a <: b -> b <: c -> a <: c.
Class SubtypeValid (A: Set) `{_Subtype: Subtype A} `{_IsValidType: IsValidType A} `{_EqvType: EqvType A}: Prop := subtype_valid: SubtypeRefl A /\ SubtypeAntisym A /\ SubtypeTrans A.
Class SubtypeValid0 (A: Set) `{_Subtype: Subtype A} `{_IsValidType: IsValidType A} `{_EqvType: EqvType A} `{_Top: Top A} `{_Bottom: Bottom A}: Prop := subtype_valid0: SubtypeTop A /\ SubtypeBottom A /\ SubtypeValid A.
(* TODO: Some of these = may need to be == *)
Class UnionTop (A: Set) `{_Subtype: Subtype A} `{_Top: Top A}: Prop := union_top: forall (a: A), top U a = top.
Class UnionBottom (A: Set) `{_Subtype: Subtype A} `{_Bottom: Bottom A}: Prop := union_bottom: forall (a: A), bottom U a = a.
Class IntersectTop (A: Set) `{_Subtype: Subtype A} `{_Top: Top A}: Prop := intersect_top: forall (a: A), top I a = a.
Class IntersectBottom (A: Set) `{_Subtype: Subtype A} `{_Bottom: Bottom A}: Prop := intersect_bottom: forall (a: A), bottom I a = bottom.
Class UnionRefl (A: Set) `{_Subtype: Subtype A} `{_IsValidType: IsValidType A}: Prop := union_refl: forall (a: A), is_valid_type a -> a U a = a.
Class IntersectRefl (A: Set) `{_Subtype: Subtype A} `{_IsValidType: IsValidType A}: Prop := intersect_refl: forall (a: A), is_valid_type a -> a I a = a.
Class UnionComm (A: Set) `{_Subtype: Subtype A}: Prop := union_comm: forall (a b ab: A), a U b = ab <-> b U a = ab.
Class IntersectComm (A: Set) `{_Subtype: Subtype A}: Prop := intersect_comm: forall (a b ab: A), a I b = ab <-> b I a = ab.
Class UnionAssoc (A: Set) `{_Subtype: Subtype A}: Prop := union_assoc: forall (a b c ab bc abc: A), a U b = ab -> b U c = bc -> ab U c = abc <-> a U bc = abc.
Class IntersectAssoc (A: Set) `{_Subtype: Subtype A}: Prop := intersect_assoc: forall (a b c ab bc abc: A), a I b = ab -> b I c = bc -> ab I c = abc <-> a I bc = abc.
Class UnionAbsorb (A: Set) `{_Subtype: Subtype A}: Prop := union_absorb: forall (a b ab: A), a <: b -> a U b = ab <-> a = ab.
Class IntersectAbsorb (A: Set) `{_Subtype: Subtype A}: Prop := intersect_absorb: forall (a b ab: A), a <: b -> a I b = ab <-> b = ab.
Class UnionIntersectValid (A: Set) `{_Subtype: Subtype A} `{_IsValidType: IsValidType A}: Prop := union_intersect_valid: UnionRefl A /\ IntersectRefl A /\ UnionComm A /\ IntersectComm A /\ UnionAssoc A /\ IntersectAssoc A /\ UnionAbsorb A /\ IntersectAbsorb A.
Class UnionIntersectValid0 (A: Set) `{_Subtype: Subtype A} `{_IsValidType: IsValidType A} `{_Top: Top A} `{_Bottom: Bottom A}: Prop := union_intersect_valid0: UnionBottom A /\ UnionTop A /\ IntersectBottom A /\ IntersectTop A /\ UnionIntersectValid A.
Class UnionSubtypeLattice0 (A: Set) `{_Subtype: Subtype A}: Prop := union_subtype_lattice0: forall (a b ab c: A), a <: c -> b <: c -> a U b = ab -> ab <: c.
Class IntersectSubtypeLattice0 (A: Set) `{_Subtype: Subtype A}: Prop := intersect_subtype_lattice0: forall (a b ab c: A), c <: a -> c <: b -> a I b = ab -> c <: ab.
Class UnionSubtypeLattice1 (A: Set) `{_Subtype: Subtype A}: Prop := union_subtype_lattice1: forall (a b c d ab cd: A), a <: c -> b <: d -> a U b = ab -> c U d = cd -> ab <: cd.
Class IntersectSubtypeLattice1 (A: Set) `{_Subtype: Subtype A}: Prop := intersect_subtype_lattice1: forall (a b c d ab cd: A), a <: c -> b <: d -> a I b = ab -> c I d = cd -> ab <: cd.
Class UnionSubtypeLattice2 (A: Set) `{_Subtype: Subtype A}: Prop := union_subtype_lattice2: forall (a b ab: A), a U b = ab -> a <: ab /\ b <: ab.
Class IntersectSubtypeLattice2 (A: Set) `{_Subtype: Subtype A}: Prop := intersect_subtype_lattice2: forall (a b ab: A), a I b = ab -> ab <: a /\ ab <: b.
Class UnionIntersectSubtypeLattice (A: Set) `{_Subtype: Subtype A} `{_Top: Top A} `{_Bottom: Bottom A}: Prop := union_intersectSubtype_lattice: UnionSubtypeLattice0 A /\ UnionSubtypeLattice1 A /\ UnionSubtypeLattice2 A /\ IntersectSubtypeLattice0 A /\ IntersectSubtypeLattice1 A /\ IntersectSubtypeLattice2 A.
Class SubtypeUnionIntersectValid (A: Set) `{_Subtype: Subtype A} `{_IsValidType: IsValidType A} `{_EqvType: EqvType A} `{_Top: Top A} `{_Bottom: Bottom A}: Prop := subtype_union_intersect_valid: SubtypeValid A /\ UnionIntersectValid A /\ UnionIntersectSubtypeLattice A.
Set Implicit Arguments.

(* Subtype relation implementations *)
Inductive S_option {A: Set} (S: Subtype A): Subtype (option A) :=
| S_None            : forall (lhs: option A), [S_option S] lhs <: None
| S_Some            : forall (lhs rhs: A), [S] lhs <: rhs -> [S_option S] Some lhs <: Some rhs
. Global Instance SOf_option {A: Set} {S: Subtype A}: Subtype (option A) := S_option S.
Inductive E_option {A: Set} (E: EqvType A) : EqvType (option A) :=
| E_None            : forall (lhs: option A), [E_option E] lhs == None
| E_Some            : forall (lhs rhs: A), [E] lhs == rhs -> [E_option E] (Some lhs) == (Some rhs)
. Global Instance EOf_option {A: Set} {E: EqvType A}: EqvType (option A) := E_option E.
Inductive S_Zip {A: Set} (S: Subtype A): Subtype (list A) :=
| S_Zip_nil          : forall (lhs: list A), [S_Zip S] lhs <: nil
| S_Zip_cons         : forall (l r: A) (ls rs: list A),
    [S] l <: r -> [S_Zip S] ls <: rs -> [S_Zip S] (l :: ls) <: (r :: rs)
(* no global instance because there is S_Intersect *)
. Definition SOf_Zip {A: Set} {S: Subtype A}: Subtype (list A) := S_Zip S.
Inductive E_Zip {A: Set} (E: EqvType A) : EqvType (list A) :=
| E_Zip_nil          : [E_Zip E] nil == nil
| E_Zip_cons         : forall (l r: A) (ls rs: list A),
    [E] l == r -> [E_Zip E] ls == rs -> [E_Zip E] (l :: ls) == (r :: rs)
. Global Instance EOf_Zip {A: Set} {E: EqvType A}: EqvType (list A) := E_Zip E.
(* no global instance because there is S_Zip and S_Intersect *)
Definition S_JsrZip {A: Set} (S: Subtype A): Subtype (js_record A) := JsRecord1Rel S.
Definition SOf_JsrZip {A: Set} {S: Subtype A}: Subtype (js_record A) := JsRecord1Rel S.
Global Instance EOf_JsrZip {A: Set} {E: EqvType A}: EqvType (js_record A) := JsRecordRel E.
Inductive S_Intersect {A: Set} (S: Subtype A): Subtype (list A) :=
| S_Intersect_nil    : forall (lhs: list A), [S_Intersect S] lhs <: nil
| S_Intersect_cons   : forall (l r: A) (ls rs: list A),
    [S] l <: r -> [S_Intersect S] ls <: rs -> [S_Intersect S] (l :: ls) <: (r :: rs)
| S_Intersect_cons_l : forall (l: A) (ls rs: list A),
                 [S_Intersect S] ls <: rs -> [S_Intersect S] (l :: ls) <: rs
(* no global instance because there is S_Zip *)
. Definition SOf_Intersect {A: Set} {S: Subtype A}: Subtype (list A) := S_Intersect S.
Inductive S_variance: Subtype variance :=
| S_Bivariant        : forall (lhs: variance), [S_variance] lhs <: Bivariant
| S_Covariant        : [S_variance] Covariant <: Covariant
| S_Contravariant    : [S_variance] Contravariant <: Contravariant
| S_Invariant        : forall (rhs: variance), [S_variance] Invariant <: rhs
. Global Instance SOf_variance: Subtype variance := S_variance.
Global Instance EOf_variance: EqvType variance := eq.
Inductive S_otype {A: Set} (S: Subtype A): Subtype (otype A) :=
| S_OType            : forall (ol or: bool) (lhs rhs: A), ol <= or -> [S] lhs <: rhs -> [S_otype S] Ot ol lhs <: Ot or rhs
. Global Instance SOf_otype {A: Set} {S: Subtype A}: Subtype (otype A) := S_otype S.
Inductive E_otype {A: Set} (E: EqvType A): EqvType (otype A) :=
| E_OType            : forall (o: bool) (lhs rhs: A), [E] lhs == rhs -> [E_otype E] Ot o lhs == Ot o rhs
. Global Instance EOf_otype {A: Set} {E: EqvType A}: EqvType (otype A) := E_otype E.
Inductive S_vtype {A: Set} (S: Subtype A): Subtype (vtype A) :=
| S_Void             : [S_vtype S] @VVoid A <: VVoid
| S_NotVoid          : forall (lhs rhs: A), [S] lhs <: rhs -> [S_vtype S] Vt lhs <: Vt rhs
. Global Instance SOf_vtype {A: Set} {S: Subtype A}: Subtype (vtype A) := S_vtype S.
Inductive E_vtype {A: Set} (E: EqvType A): EqvType (vtype A) :=
| E_Void             : [E_vtype E] @VVoid A == VVoid
| E_NotVoid          : forall (lhs rhs: A), [E] lhs == rhs -> [E_vtype E] Vt lhs == Vt rhs
. Global Instance EOf_vtype {A: Set} {E: EqvType A}: EqvType (vtype A) := E_vtype E.
Inductive S_tparam {A: Set} (S: Subtype A): Subtype (tparam A) :=
| S_TParam           : forall (vl vr: variance) (name: string) (supl supr: list A),
    [S_variance] vl <: vr -> [S_Intersect S] supl <: supr ->
    [S_tparam S] TParam vl name supl <: TParam vr name supr
. Global Instance SOf_tparam {A: Set} {S: Subtype A}: Subtype (tparam A) := S_tparam S.
Inductive E_tparam {A: Set} (E: EqvType A): EqvType (tparam A) :=
| E_TParam           : forall (v: variance) (name: string) (supl supr: list A),
    [E_Zip E] supl == supr -> [E_tparam E] TParam v name supl == TParam v name supr
. Global Instance EOf_tparam {A: Set} {E: EqvType A}: EqvType (tparam A) := E_tparam E.
Inductive S_itype {A: Set} (S: Subtype A): Subtype (itype A) :=
| S_Ident            : forall (name: string) (tal tar: list A), [S_Zip S] tal <: tar -> [S_itype S] It name tal <: It name tar
. Global Instance SOf_itype {A: Set} {S: Subtype A}: Subtype (itype A) := S_itype S.
Inductive E_itype {A: Set} (E: EqvType A): EqvType (itype A) :=
| E_Ident            : forall (name: string) (tal tar: list A), [E_Zip E] tal == tar -> [E_itype E] It name tal == It name tar
. Global Instance EOf_itype {A: Set} {E: EqvType A}: EqvType (itype A) := E_itype E.
Inductive S_stype {A: Set} (S: Subtype A): Subtype (stype A) :=
| S_Fn               : forall (tpl tpr: list (tparam A)) (thispl thispr: A)
                         (pl pr: list (otype A)) (rl rr: A) (retl retr: (vtype A)),
    [S_Zip (S_tparam S)] tpl :> tpr -> [S] thispl :> thispr -> [S_Zip (S_otype S)] pl :> pr -> [S] rl :> rr -> [S_vtype S] retl <: retr ->
    [S_stype S] SFn tpl thispl pl rl retl <: SFn tpr thispr pr rr retr
| S_Array            : forall (el er: A),                     [S]                     el <: er  -> [S_stype S] SArray el   <: SArray er
| S_Tuple            : forall (esl esr: list (otype A)),      [S_Zip (S_otype S)]    esl <: esr -> [S_stype S] STuple esl  <: STuple esr
| S_Object           : forall (fsl fsr: js_record (otype A)), [S_JsrZip (S_otype S)] fsl <: fsr -> [S_stype S] SObject fsl <: SObject fsr
. Global Instance SOf_stype {A: Set} {S: Subtype A}: Subtype (stype A) := S_stype S.
Inductive E_stype {A: Set} (E: EqvType A): EqvType (stype A) :=
| E_Fn               : forall (tpl tpr: list (tparam A)) (thispl thispr: A)
                         (pl pr: list (otype A)) (rl rr: A) (retl retr: (vtype A)),
    [E_Zip (E_tparam E)] tpl == tpr -> [E] thispl == thispr -> [E_Zip (E_otype E)] pl == pr -> [E] rl == rr -> [E_vtype E] retl == retr ->
    [E_stype E] SFn tpl thispl pl rl retl == SFn tpr thispr pr rr retr
| E_Array            : forall (el er: A),                     [E]                     el == er  -> [E_stype E] SArray el   == SArray er
| E_Tuple            : forall (esl esr: list (otype A)),      [E_Zip (E_otype E)]    esl == esr -> [E_stype E] STuple esl  == STuple esr
| E_Object           : forall (fsl fsr: js_record (otype A)), [JsRecordRel (E_otype E)] fsl == fsr -> [E_stype E] SObject fsl == SObject fsr
. Global Instance EOf_stype {A: Set} {E: EqvType A}: EqvType (stype A) := E_stype E.
Inductive S_ftype: Subtype ftype :=
| S_Any              : forall (lhs: ftype), [S_ftype] lhs <: FAny
| S_Never            : forall (rhs: ftype), [S_ftype] FNEVER <: rhs
| S_Null             : forall (rhs: ftype), IsNullable rhs -> [S_ftype] FNULL <: rhs
| S_Struct           : forall (nl nr: bool) (sl sr: sftype),
    nl <= nr -> [S_stype S_ftype] sl <: sr -> [S_ftype] FStructural nl sl <: FStructural nr sr
| S_NomStruct        : forall (nl nr: bool) (idl: iftype) (idsl: list iftype) (sl sr: sftype),
    nl <= nr -> [S_stype S_ftype] sl <: sr -> [S_ftype] FNominal nl idl idsl (Some sl) <: FStructural nr sr
| S_Nom              : forall (nl nr: bool) (idl idr: iftype) (idsl idsr: list iftype) (sl sr: option sftype),
    nl <= nr -> [S_Intersect (S_itype S_ftype)] (idl :: idsl) <: (idr :: idsr) -> [S_option (S_stype S_ftype)] sl <: sr ->
    [S_ftype] FNominal nl idl idsl sl <: FNominal nr idr idsr sr
. Global Instance SOf_ftype: Subtype ftype := S_ftype.
Inductive E_ftype: EqvType ftype :=
| E_Any              : [E_ftype] FAny == FAny
| E_NeverNull        : forall (n: bool), [E_ftype] FNever n == FNever n
| E_Struct           : forall (n: bool) (sl sr: sftype),
    [E_stype E_ftype] sl == sr -> [E_ftype] FStructural n sl == FStructural n sr
| E_Nom              : forall (n: bool) (idl idr: iftype) (idsl idsr: list iftype) (sl sr: option sftype),
    [E_Zip (E_itype E_ftype)] (idl :: idsl) == (idr :: idsr) -> [E_option (E_stype E_ftype)] sl == sr ->
    [E_ftype] FNominal n idl idsl sl == FNominal n idr idsr sr
. Global Instance EOf_ftype: EqvType ftype := E_ftype.

(* An axiom needed for induction because of complex recursion *)
Axiom S_ftype_ind':
  forall (P: Subtype ftype)
    (fS_Any: forall lhs : ftype, P lhs FAny)
    (fS_Never: forall rhs : ftype, P FNEVER rhs)
    (fS_Null: forall rhs : ftype, IsNullable rhs -> P FNULL rhs)
    (fS_Struct: forall (nl nr : bool) (sl sr : sftype),
      nl <= nr ->
      [S_stype P] sl <: sr ->
      P (FStructural nl sl) (FStructural nr sr))
    (fS_NomStruct: forall (nl nr : bool) (idl : iftype) (idsl : list iftype) (sl sr : sftype),
      nl <= nr ->
      [S_stype P] sl <: sr ->
      P (FNominal nl idl idsl (Some sl)) (FStructural nr sr))
    (fS_Nom: forall (nl nr : bool) (idl idr idu : iftype) (idsl idsr idsu : list iftype)
        (sl sr su : option sftype),
      nl <= nr ->
      [S_Intersect (S_itype P)] (idl :: idsl) <: (idr :: idsr) ->
      [S_option (S_stype P)] sl <: sr ->
      P (FNominal nl idl idsl sl) (FNominal nr idr idsr sr))
    (lhs rhs: ftype), S_ftype lhs rhs -> P lhs rhs.
Axiom E_ftype_ind':
  forall (P: EqvType ftype)
    (fE_Any: P FAny FAny)
    (fE_NeverNull: forall (n : bool), P (FNever n) (FNever n))
    (fE_Struct: forall (n : bool) (sl sr : sftype),
      [E_stype P] sl == sr -> P (FStructural n sl) (FStructural n sr))
    (fE_Nom: forall (n : bool) (idl idr idu : iftype) (idsl idsr idsu : list iftype) (sl sr su : option sftype),
      [E_Zip (E_itype P)] (idl :: idsl) == (idr :: idsr) ->
      [E_option (E_stype P)] sl == sr ->
      P (FNominal n idl idsl sl) (FNominal n idr idsr sr))
    (lhs rhs: ftype), E_ftype lhs rhs -> P lhs rhs.

(* Now we prove that these relations are valid *)
Global Instance Top_option {A: Set} `{_Top: Top A}: Top (option A) := None.
Global Instance Bottom_option {A: Set} `{_Bottom: Bottom A}: Bottom (option A) := Some bottom.
Global Instance IsValidType_option {A: Set} `{V: IsValidType A}: IsValidType (option A) := Option_Forall V.
Global Instance SubtypeRefl_option {A: Set} `(_SubtypeRefl: SubtypeRefl A): SubtypeRefl (option A).
Proof. intros a; destruct a; constructor; apply subtype_refl; inv H; assumption. Qed.
Global Instance SubtypeAntisym_option {A: Set} `(_SubtypeAntisym: SubtypeAntisym A): SubtypeAntisym (option A).
Proof. intros a b H H0; destruct a, b; inv H H0; constructor; apply subtype_antisym; assumption. Qed.
Global Instance SubtypeTrans_option {A: Set} `{_SubtypeTrans: SubtypeTrans A}: SubtypeTrans (option A).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; apply subtype_trans with a0; assumption. Qed.

Global Instance IsValidType_list {A: Set} `{V: IsValidType A}: IsValidType (list A) := List.Forall V.
Global Instance SubtypeRefl_Zip {A: Set} `{_SubtypeRefl: SubtypeRefl A}: @SubtypeRefl (list A) SOf_Zip IsValidType_list.
Proof. intros a; induction a; constructor; [apply subtype_refl | apply IHa]; inv H; assumption. Qed.
Global Instance SubtypeAntisym_Zip {A: Set} `{_SubtypeAntisym: SubtypeAntisym A}: @SubtypeAntisym (list A) SOf_Zip EOf_Zip.
Proof. intros a b H H0; (induction2 a b using ind_list2); [inv H H0 | inv H0 H1 .. ]; constructor; [apply subtype_antisym | apply H]; assumption. Qed.
Global Instance SubtypeTrans_Zip {A: Set} `{_SubtypeTrans: SubtypeTrans A}: @SubtypeTrans (list A) SOf_Zip.
Proof. intros a b c H H0; (induction3 a b c using ind_list3); [inv H H0 | inv H0 H1 ..]; constructor; [apply subtype_trans with y | apply H]; assumption. Qed.

Global Instance IsValidType_js_record {A: Set} `{V: IsValidType A}: IsValidType (js_record A) := JsRecordNoDupForall V.
Global Instance SubtypeRefl_JsrZip {A: Set} `{_SubtypeRefl: SubtypeRefl A}: @SubtypeRefl (js_record A) SOf_JsrZip IsValidType_js_record.
Proof. intros a; induction a; [constructor; constructor |]; destruct a as [ka va]; intros; apply JsRecord1Rel_cons with va a0; [apply subtype_refl | apply IHa | apply JsRecordAdd_head |]; inv H; assumption. Qed.
Global Instance SubtypeAntisym_JsrZip {A: Set} `{_SubtypeAntisym: SubtypeAntisym A}: @SubtypeAntisym (js_record A) SOf_JsrZip EOf_JsrZip.
Proof.
  intros a b H H0; pose (JsRecord1Rel_In H); pose (JsRecord1Rel_In H0); apply JsRecordRel_In0; try assumption.
  - eapply proj1, JsRecord1Rel_NoDup; exact H.
  - eapply proj1, JsRecord1Rel_NoDup; exact H0.
  - split; intros; [apply (@JsRecord1Rel_HasKey A _Subtype) with a | apply (@JsRecord1Rel_HasKey A _Subtype) with b]; assumption.
  - intros; apply subtype_antisym; [apply _s with k | apply _s0 with k]; assumption.
Qed.
Global Instance SubtypeTrans_JsrZip {A: Set} `{_SubtypeTrans: SubtypeTrans A}: @SubtypeTrans (js_record A) SOf_JsrZip.
Proof.
  intros a b c H H0; pose (JsRecord1Rel_In H); pose (JsRecord1Rel_In H0); apply JsRecord1Rel_In0; try assumption.
  - eapply proj1, JsRecord1Rel_NoDup; exact H.
  - eapply proj2, JsRecord1Rel_NoDup; exact H0.
  - intros; apply (@JsRecord1Rel_HasKey A _Subtype) with b, (@JsRecord1Rel_HasKey A _Subtype) with c; assumption.
  - intros; destruct (JsRecordHasKey_dec k b); [| contradict H3; apply (@JsRecord1Rel_HasKey A _Subtype) with c; [| apply JsRecordHasKey_In0 with vy]; assumption]; rewrite JsRecordHasKey_In in H3; destruct H3 as [vb H3].
    apply subtype_trans with vb; [apply _s with k | apply _s0 with k]; assumption.
Qed.

Lemma S_Intersect_length {A: Set} {S: Subtype A}: forall (xs ys: list A), [S_Intersect S] xs <: ys -> (List.length ys <= List.length xs)%nat.
Proof. induction 1; simpl; [apply Nat.le_0_l | rewrite <- Nat.succ_le_mono | apply Nat.le_le_succ_r]; exact IHS_Intersect. Qed.
Lemma S_Intersect_length_antisym {A: Set} {S: Subtype A}: forall (xs ys: list A), [S_Intersect S] xs <: ys -> [S_Intersect S] ys <: xs -> (List.length xs = List.length ys)%nat.
Proof. intros; apply Nat.le_antisymm; apply S_Intersect_length; assumption. Qed.
Local Ltac discr_on_intersect_length := lazymatch goal with | H: [S_Intersect _] _ <: _, H0: [S_Intersect _] _ <: _ |- _ => let e := fresh "e" in let e0 := fresh "e0" in pose' (S_Intersect_length H) as e; pose' (S_Intersect_length H0) as e0; simpl in e, e0 end; lia.

Global Instance SubtypeRefl_Intersect {A: Set} `{_SubtypeRefl: SubtypeRefl A}: @SubtypeRefl (list A) SOf_Intersect IsValidType_list.
Proof. intros a; induction a; constructor; [apply subtype_refl | apply IHa]; inv H; assumption. Qed.
Global Instance SubtypeAntisym_Intersect {A: Set} `{_SubtypeAntisym: SubtypeAntisym A}: @SubtypeAntisym (list A) SOf_Intersect EOf_Zip.
Proof.
  intros a b H H0; pose' (S_Intersect_length_antisym H H0); (induction2 a b using ind_list2); simpl in e;
    [constructor | discriminate e | discriminate e |]; inv e H0 H1; try discr_on_intersect_length;
    constructor; [apply subtype_antisym | apply H]; assumption.
Qed.
Global Instance SubtypeTrans_Intersect {A: Set} `{_SubtypeTrans: SubtypeTrans A}: @SubtypeTrans (list A) SOf_Intersect.
Proof.
  intros a; induction a; try rename a into a0, a0 into a; induction b; try rename a1 into b0; induction c; try rename a1 into c0; intros;
    try (inv H H0; fail); [constructor .. |]; inv H H0;
    [constructor; [apply subtype_trans with b0 | apply IHa with b] | apply IHb; [constructor |] | constructor; apply IHa with (b0 :: b); [| constructor] ..]; assumption.
Qed.

Global Instance Top_variance: Top variance := Bivariant.
Global Instance Bottom_variance: Bottom variance := Invariant.
Global Instance IsValidType_variance: IsValidType variance := IsValidType_always.
Global Instance SubtypeRefl_variance: SubtypeRefl variance.
Proof. intros a; destruct a; constructor. Qed.
Global Instance SubtypeAntisym_variance: SubtypeAntisym variance.
Proof. intros a b H H0; destruct a, b; inv H H0; constructor. Qed.
Global Instance SubtypeTrans_variance: SubtypeTrans variance.
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor. Qed.

(* TODO rest of the relations *)
Global Instance Top_otype {A: Set} `{_Top: Top A}: Top (otype A) := Ot true _Top.
Global Instance Bottom_otype {A: Set} `{_Bottom: Bottom A}: Bottom (otype A) := Ot false _Bottom.
Global Instance IsValidType_otype {A: Set} `{V: IsValidType A}: IsValidType (otype A) := fun '(Ot _ a) => V a.
Global Instance SubtypeRefl_otype {A: Set} `{_SubtypeRefl: SubtypeRefl A}: SubtypeRefl (otype A).
Proof. intros a; destruct a; constructor; [destruct optional; simpl; reflexivity | apply subtype_refl]; assumption. Qed.
Global Instance SubtypeAntisym_otype {A: Set} `{_SubtypeAntisym: SubtypeAntisym A}: SubtypeAntisym (otype A).
Proof. intros a b H H0; destruct a, b; inv H H0; destruct optional, optional0; try discriminate; constructor; apply subtype_antisym; assumption. Qed.
Global Instance SubtypeTrans_otype {A: Set} `{_SubtypeTrans: SubtypeTrans A}: SubtypeTrans (otype A).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; destruct optional, optional0, optional1; try discriminate; constructor; (simpl; reflexivity) || apply subtype_trans with a0; assumption. Qed.

Global Instance IsValidType_vtype {A: Set} `{V: IsValidType A}: IsValidType (vtype A) := fun a => match a with | VVoid => True | Vt a => V a end.
Global Instance SubtypeRefl_vtype {A: Set} `{_SubtypeRefl: SubtypeRefl A}: SubtypeRefl (vtype A).
Proof. intros a; destruct a; constructor; apply subtype_refl; assumption. Qed.
Global Instance SubtypeAntisym_vtype {A: Set} `{_SubtypeAntisym: SubtypeAntisym A}: SubtypeAntisym (vtype A).
Proof. intros a b H H0; destruct a, b; inv H H0; constructor; apply subtype_antisym; assumption. Qed.
Global Instance SubtypeTrans_vtype {A: Set} `{_SubtypeTrans: SubtypeTrans A}: SubtypeTrans (vtype A).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; apply subtype_trans with a0; assumption. Qed.

Global Instance IsValidType_tparam {A: Set} `{V: IsValidType A}: IsValidType (tparam A) := fun '(TParam _ _ supers) => @IsValidType_list A V supers.
Global Instance SubtypeRefl_tparam {A: Set} `{_SubtypeRefl: SubtypeRefl A}: SubtypeRefl (tparam A).
Proof. intros a; destruct a; constructor; apply subtype_refl; [reflexivity | assumption]. Qed.
Global Instance SubtypeAntisym_tparam {A: Set} `{_SubtypeAntisym: SubtypeAntisym A}: SubtypeAntisym (tparam A).
Proof. intros a b H H0; destruct a, b; inv H H0; rewrite (SubtypeAntisym_variance H2 H3); constructor; apply SubtypeAntisym_Intersect; assumption. Qed.
Global Instance SubtypeTrans_tparam {A: Set} `{_SubtypeTrans: SubtypeTrans A}: SubtypeTrans (tparam A).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; [apply subtype_trans with v0 | apply subtype_trans with supers0]; assumption. Qed.

Global Instance IsValidType_itype {A: Set} `{V: IsValidType A}: IsValidType (itype A) := fun '(It _ targs) => @IsValidType_list A V targs.
Global Instance SubtypeRefl_itype {A: Set} `{_SubtypeRefl: SubtypeRefl A}: SubtypeRefl (itype A).
Proof. intros a; destruct a; constructor; apply subtype_refl; assumption. Qed.
Global Instance SubtypeAntisym_itype {A: Set} `{_SubtypeAntisym: SubtypeAntisym A}: SubtypeAntisym (itype A).
Proof. intros a b H H0; destruct a, b; inv H H0; constructor; apply SubtypeAntisym_Zip; assumption. Qed.
Global Instance SubtypeTrans_itype {A: Set} `{_SubtypeTrans: SubtypeTrans A}: SubtypeTrans (itype A).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; apply subtype_trans with targs0; assumption. Qed.

Global Instance IsValidType_stype {A: Set} `{V: IsValidType A}: IsValidType (stype A) := fun x => match x with
| SFn tparams thisp params restp ret => is_valid_type tparams /\ is_valid_type thisp /\ is_valid_type params /\ is_valid_type restp /\ is_valid_type ret
| SArray elem => is_valid_type elem
| STuple elems => is_valid_type elems
| SObject fields => is_valid_type fields
end.
Global Instance SubtypeRefl_stype {A: Set} `{_SubtypeRefl: SubtypeRefl A}: SubtypeRefl (stype A).
Proof. intros a; destruct a; constructor; apply subtype_refl; unfold is_valid_type, IsValidType_stype in H; decompose [and] H; assumption. Qed.
Global Instance SubtypeAntisym_stype {A: Set} `{_SubtypeAntisym: SubtypeAntisym A}: SubtypeAntisym (stype A).
Proof. intros a b H H0; destruct a, b; inv H H0; constructor; apply subtype_antisym || apply SubtypeAntisym_Zip || apply SubtypeAntisym_JsrZip; assumption. Qed.
Global Instance SubtypeTrans_stype {A: Set} `{_SubtypeTrans: SubtypeTrans A}: SubtypeTrans (stype A).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; eapply subtype_trans; eassumption. Qed.

Definition IsValidType_ftype (x: ftype): Prop.
  induction x using ftype_ind'.
  - exact True.
  - exact True.
  - apply (@IsValidType_stype ftype); assumption.
  - apply and; [apply and |]; [apply (@IsValidType_itype ftype) | apply (@IsValidType_list iftype); [apply (@IsValidType_itype ftype) |] | apply (@IsValidType_option sftype); [apply (@IsValidType_stype ftype) |]]; assumption.
Qed.

From Equations Require Import Equations.
Equations _IsValidType_ftype (x: ftype): Prop by wf (ftype_depth x) lt :=
_IsValidType_ftype FAny := True;
_IsValidType_ftype (FNever _) := True;
_IsValidType_ftype (FStructural _ structure) := @IsValidType_stype ftype (fun a => _IsValidType_ftype a) structure;
_IsValidType_ftype (FNominal _ id sids structure) := @IsValidType_itype ftype (fun a => _IsValidType_ftype a) id /\ @IsValidType_list iftype (@IsValidType_itype ftype (fun a => _IsValidType_ftype a)) sids /\ @IsValidType_option sftype (@IsValidType_stype ftype (fun a => _IsValidType_ftype a)) structure.
Next Obligation. auto.
Program Fixpoint _IsValidType_ftype (x: ftype) {measure (ftype_depth x)}: Prop := match x with
| FAny => True
| FNever _ => True
| FStructural _ structure => @IsValidType_stype ftype (fun a => _IsValidType_ftype a) structure
| FNominal _ id sids structure => @IsValidType_itype ftype (fun a => _IsValidType_ftype a) id /\ @IsValidType_list iftype (@IsValidType_itype ftype (fun a => _IsValidType_ftype a)) sids /\ @IsValidType_option sftype (@IsValidType_stype ftype (fun a => _IsValidType_ftype a))  structure
end.
Next Obligation. simpl.

Global Instance IsValidType_ftype: IsValidType ftype := _IsValidType_ftype.
Global Instance SubtypeRefl_ftype {A: Set}: SubtypeRefl ftype.
Proof. intros a; destruct a; constructor; apply subtype_refl; unfold is_valid_type, IsValidType_ftype in H; decompose [and] H; assumption. Qed.
Global Instance SubtypeAntisym_ftype {A: Set}: SubtypeAntisym ftype.
Proof. intros a b H H0; destruct a, b; inv H H0; constructor; apply subtype_antisym || apply SubtypeAntisym_Zip || apply SubtypeAntisym_JsrZip; assumption. Qed.
Global Instance SubtypeTrans_ftype {A: Set}: SubtypeTrans ftype.
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; eapply subtype_trans; eassumption. Qed.
