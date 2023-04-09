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
Inductive S_JsrZip {A: Set} (S: Subtype A): Subtype (js_record A) :=
| S_JsrZip_nil       : forall (lhs: js_record A), JsRecordNoDup lhs -> [S_JsrZip S] lhs <: nil
| S_JsrZip_cons      : forall (k: string) (vl vr: A) (ls rs rs': js_record A),
    [S] vl <: vr -> [S_JsrZip S] ls <: rs -> JsRecordAdd k vr rs rs' -> ~JsRecordHasKey k ls -> [S_JsrZip S] ((k, vl) :: ls) <: rs'
| S_JsrZip_cons_r    : forall (k: string) (vl: A) (ls rs: js_record A),
                   [S_JsrZip S] ls <: rs -> ~JsRecordHasKey k rs    -> ~JsRecordHasKey k ls -> [S_JsrZip S] ((k, vl) :: ls) <: rs
(* no global instance because there is S_Zip and S_Intersect *)
. Definition SOf_JsrZip {A: Set} {S: Subtype A}: Subtype (js_record A) := S_JsrZip S.
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

Lemma S_JsrZip_NoDup: forall {A: Set} {S: Subtype A} (xs ys: js_record A),
    [S_JsrZip S] xs <: ys -> JsRecordNoDup xs /\ JsRecordNoDup ys.
Proof.
  induction 1; [| destruct IHS_JsrZip ..]; split;
    [| constructor | constructor | apply JsRecordAdd_NoDup with k vr rs | constructor |]; assumption.
Qed.

Lemma S_JsrZip_HasKey: forall {A: Set} {S: Subtype A} (k: string) (xs ys: js_record A),
    [S_JsrZip S] xs <: ys -> JsRecordHasKey k ys -> JsRecordHasKey k xs.
Proof.
  induction 1; intros; [inv H0 | |]; destruct (string_dec k k0); subst.
  - apply List.Exists_cons_hd; reflexivity.
  - apply List.Exists_cons_tl; apply IHS_JsrZip; apply JsRecordAdd_HasKey1 with k0 vr rs'; [exact H1 | exact H3 | intros n'; symmetry in n'; contradiction (n n')].
  - apply List.Exists_cons_hd; reflexivity.
  - apply List.Exists_cons_tl; apply IHS_JsrZip; exact H2.
Qed.

Lemma S_JsrZip_HasKey_neg: forall {A: Set} {S: Subtype A} (k: string) (xs ys: js_record A),
    [S_JsrZip S] xs <: ys -> ~JsRecordHasKey k xs -> ~JsRecordHasKey k ys.
Proof.
  intros; intros n; contradict H0; apply S_JsrZip_HasKey with ys; assumption.
Qed.

Lemma S_JsrZip_In_rev: forall {A: Set} {S: Subtype A} (k: string) (vx vy: A) (xs ys: js_record A),
    [S_JsrZip S] xs <: ys -> List.In (k, vx) xs -> List.In (k, vy) ys -> [S] vx <: vy.
Proof.
  intros; induction H; [inv H1 | | shelve]; inv H3; destruct (string_dec k0 k); subst.
  - apply JsRecordHasKey_In_cons in H1; [| exact H5]; apply JsRecordHasKey_In_cons in H0; [| exact H4]; subst. exact H.
  - inv H0 H1; try (inv H3 + inv H0; contradiction n; reflexivity); exact (IHS_JsrZip H3 H0).
  - apply JsRecordHasKey_In_cons in H0; [| exact H4]; inv H1; [inv H3; contradiction H5; reflexivity |]; rewrite (JsRecordAdd_In_once _ H6 H3) in *; exact H.
  - inv H0 H1; try (inv H3 + inv H0; contradiction n; reflexivity).
    + inv H0; apply IHS_JsrZip; [exact H3 | simpl; left; reflexivity].
    + pose (JsRecordAdd_In_once' _ _ H6 H0); apply i in n; apply IHS_JsrZip; [exact H3 | simpl; right; exact n].
Unshelve.
  inv H0.
  * inv H4; contradict H3; apply S_JsrZip_HasKey with rs; [exact H |]; apply JsRecordHasKey_In0 with vy; assumption.
  * apply IHS_JsrZip; assumption.
Qed.

Lemma S_JsrZip_add0: forall {A: Set} {S: Subtype A} (k: string) (vx vy: A) (xs xs' ys ys': js_record A),
    JsRecordAdd k vx xs xs' -> JsRecordAdd k vy ys ys' -> [S_JsrZip S] xs' <: ys' -> [S] vx <: vy.
Proof.
  intros. apply JsRecordAdd_In in H, H0; eapply S_JsrZip_In_rev in H1; [exact H1 | exact H | exact H0].
Qed.

Lemma S_JsrZip_In: forall {A: Set} {S: Subtype A} (xs ys: js_record A),
    [S_JsrZip S] xs <: ys -> forall (k: string) (vx vy: A), List.In (k, vx) xs -> List.In (k, vy) ys -> vx <: vy.
Proof.
  induction xs; intros; [inv H0 |]; destruct a as [kx0 vx0]; inv H0.
  - inv H H2; [inv H1 | rewrite (JsRecordAdd_In_once _ H8 H1) in *; exact H5 | ]; contradict H8; apply S_JsrZip_HasKey with ys; [exact H5 |]; apply JsRecordHasKey_In0 with vy; exact H1.
  - destruct (string_dec kx0 k); [subst; inv H; [inv H1 | contradict H9 | contradict H8]; apply JsRecordHasKey_In0 with vx; exact H2 |].
    inv H; [inv H1 | apply IHxs with rs k; try assumption; apply JsRecordAdd_In_once' with kx0 vr ys; assumption | apply IHxs with ys k; assumption].
Qed.

Theorem S_JsrZip_In0: forall {A: Set} {S: Subtype A} (xs ys: js_record A),
    JsRecordNoDup xs -> JsRecordNoDup ys -> (forall k, JsRecordHasKey k ys -> JsRecordHasKey k xs) ->
    (forall (k: string) (vx vy: A), List.In (k, vx) xs -> List.In (k, vy) ys -> vx <: vy) ->
    [S_JsrZip S] xs <: ys.
Proof.
  induction xs; intros; [destruct ys; [apply S_JsrZip_nil; constructor | destruct p as [ky vy]; specialize (H1 ky); assert_specialize H1; [apply List.Exists_cons_hd; reflexivity | inv H1]] |]; destruct a as [k vx].
  destruct (JsRecordHasKey_dec k ys).
  - apply JsRecordAdd_from_HasKey in H3; [| assumption]; destruct H3 as [vy [ys0 H3]]; inv H.
    apply S_JsrZip_cons with vy ys0; [apply H2 with k | apply IHxs | ..]; try assumption.
    + left; reflexivity.
    + apply JsRecordAdd_In with ys0; assumption.
    + eapply proj2; apply JsRecordAdd_NoDup_rev with vy ys; [assumption | exact H3].
    + intros; specialize (H1 k0); destruct (string_dec k0 k).
      * subst; apply JsRecordAdd_not_HasKey in H3; contradiction.
      * eapply JsRecordHasKey_uncons1; [apply H1 | exact n]; apply JsRecordAdd_HasKey0 with k vy ys0; assumption.
    + intros; specialize (H2 k0 vx0 vy0); destruct (string_dec k0 k); [| apply H2].
      * subst; contradict H8; apply JsRecordHasKey_In0 with vx0; assumption.
      * right; assumption.
      * apply JsRecordAdd_In0 with k vy ys0; assumption.
  - inv H; apply S_JsrZip_cons_r; [apply IHxs | |]; try assumption.
    + intros; specialize (H1 k0 H); inv H1; [contradiction | assumption].
    + intros; specialize (H2 k0 vx0 vy); destruct (string_dec k0 k); [| apply H2].
      * subst; contradict H8; apply JsRecordHasKey_In0 with vx0; assumption.
      * right; assumption.
      * assumption.
Qed.

Global Instance IsValidType_js_record {A: Set} `{V: IsValidType A}: IsValidType (js_record A) := JsRecordNoDupForall V.
Global Instance SubtypeRefl_JsrZip {A: Set} `{_SubtypeRefl: SubtypeRefl A}: @SubtypeRefl (js_record A) SOf_JsrZip IsValidType_js_record.
Proof. intros a; induction a; [constructor; constructor |]; destruct a as [ka va]; intros; apply S_JsrZip_cons with va a0; [apply subtype_refl | apply IHa | apply JsRecordAdd_head |]; inv H; assumption. Qed.
Global Instance SubtypeAntisym_JsrZip {A: Set} `{_SubtypeAntisym: SubtypeAntisym A}: @SubtypeAntisym (js_record A) SOf_JsrZip EOf_JsrZip.
Proof.
  intros a b H H0; pose (S_JsrZip_In H); pose (S_JsrZip_In H0); apply JsRecordRel_In0; try assumption.
  - eapply proj1, S_JsrZip_NoDup; exact H.
  - eapply proj1, S_JsrZip_NoDup; exact H0.
  - split; intros; [apply S_JsrZip_HasKey with a | apply S_JsrZip_HasKey with b]; assumption.
  - intros; apply subtype_antisym; [apply s with k | apply s0 with k]; assumption.
Qed.
Global Instance SubtypeTrans_JsrZip {A: Set} `{_SubtypeTrans: SubtypeTrans A}: @SubtypeTrans (js_record A) SOf_JsrZip.
Proof.
  intros a b c H H0; pose (S_JsrZip_In H); pose (S_JsrZip_In H0); apply S_JsrZip_In0; try assumption.
  - eapply proj1, S_JsrZip_NoDup; exact H.
  - eapply proj2, S_JsrZip_NoDup; exact H0.
  - intros; apply S_JsrZip_HasKey with b, S_JsrZip_HasKey with c; assumption.
  - intros; destruct (JsRecordHasKey_dec k b); [| contradict H3; apply S_JsrZip_HasKey with c; [| apply JsRecordHasKey_In0 with vy]; assumption]; rewrite JsRecordHasKey_In in H3; destruct H3 as [vb H3].
    apply subtype_trans with vb; [apply s with k | apply s0 with k]; assumption.
Qed.

