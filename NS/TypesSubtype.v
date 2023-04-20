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

Definition Union {A: Set} {S: Subtype A} (lhs rhs uni: A): Prop := lhs <: uni /\ rhs <: uni /\ forall a, lhs <: a -> rhs <: a -> uni <: a.
Notation "'(U)'" := Union.
Notation "lhs 'U' rhs '=' uni" := (Union lhs rhs uni) (at level 60, rhs at next level, no associativity).

Definition Intersection {A: Set} {S: Subtype A} (lhs rhs int: A): Prop := int <: lhs /\ int <: rhs /\ forall a, a <: lhs -> a <: rhs -> a <: int.
Notation "'(I)'" := Intersection.
Notation "lhs 'I' rhs '=' uni" := (Intersection lhs rhs uni) (at level 60, rhs at next level, no associativity).

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
Class SubtypeTop {A: Set} `(S: Subtype A) `{T: Top A}: Prop := subtype_top: forall (a: A), a <: top.
Class SubtypeBottom {A: Set} `(S: Subtype A) `{B: Bottom A}: Prop := subtype_bottom: forall (a: A), bottom <: a.
Class SubtypeRefl {A: Set} `(S: Subtype A) `{V: IsValidType A}: Prop := subtype_refl: forall (a: A), is_valid_type a -> a <: a.
Class SubtypeAntisym {A: Set} `(S: Subtype A) `{E: EqvType A}: Prop := subtype_antisym: forall (a b: A), a <: b -> b <: a -> a == b.
Class SubtypeTrans {A: Set} `(S: Subtype A): Prop := subtype_trans: forall (a b c: A), a <: b -> b <: c -> a <: c.
Class SubtypeValid {A: Set} `(S: Subtype A) `{V: IsValidType A, E: EqvType A}: Prop := subtype_valid: SubtypeRefl S /\ SubtypeAntisym S /\ SubtypeTrans S.
Class SubtypeValid0 {A: Set} `(S: Subtype A) `{V: IsValidType A, E: EqvType A, T: Top A, B: Bottom A}: Prop := subtype_valid0: SubtypeTop S /\ SubtypeBottom S /\ SubtypeValid S.
Class UnionTop {A: Set} `(S: Subtype A) `{T: Top A}: Prop := union_top: forall (a: A), top U a = top.
Class UnionBottom {A: Set} `(S: Subtype A) `{B: Bottom A, V: IsValidType A}: Prop := union_bottom: forall (a: A), is_valid_type a -> bottom U a = a.
Class IntersectTop {A: Set} `(S: Subtype A) `{T: Top A, V: IsValidType A}: Prop := intersect_top: forall (a: A), is_valid_type a -> top I a = a.
Class IntersectBottom {A: Set} `(S: Subtype A) `{B: Bottom A}: Prop := intersect_bottom: forall (a: A), bottom I a = bottom.
Class UnionRefl {A: Set} `(S: Subtype A) `{V: IsValidType A}: Prop := union_refl: forall (a: A), is_valid_type a -> a U a = a.
Class IntersectRefl {A: Set} `(S: Subtype A) `{V: IsValidType A}: Prop := intersect_refl: forall (a: A), is_valid_type a -> a I a = a.
Class UnionComm {A: Set} `(S: Subtype A): Prop := union_comm: forall (a b ab: A), a U b = ab <-> b U a = ab.
Class IntersectComm {A: Set} `(S: Subtype A): Prop := intersect_comm: forall (a b ab: A), a I b = ab <-> b I a = ab.
Class UnionAssoc {A: Set} `(S: Subtype A): Prop := union_assoc: forall (a b c ab bc abc: A), a U b = ab -> b U c = bc -> ab U c = abc <-> a U bc = abc.
Class IntersectAssoc {A: Set} `(S: Subtype A): Prop := intersect_assoc: forall (a b c ab bc abc: A), a I b = ab -> b I c = bc -> ab I c = abc <-> a I bc = abc.
Class UnionAbsorb {A: Set} `(S: Subtype A) `{V: IsValidType A}: Prop := union_absorb: forall (a b ab: A), is_valid_type b -> a <: b -> a U b = b.
Class IntersectAbsorb {A: Set} `(S: Subtype A) `{V: IsValidType A}: Prop := intersect_absorb: forall (a b ab: A), is_valid_type a -> a <: b -> a I b = a.
Class UnionIntersectValid {A: Set} `(S: Subtype A) `{V: IsValidType A}: Prop := union_intersect_valid: UnionRefl S /\ IntersectRefl S /\ UnionComm S /\ IntersectComm S /\ UnionAssoc S /\ IntersectAssoc S /\ UnionAbsorb S /\ IntersectAbsorb S.
Class UnionIntersectValid0 {A: Set} `(S: Subtype A) `{V: IsValidType A, T: Top A, B: Bottom A}: Prop := union_intersect_valid0: UnionBottom S /\ UnionTop S /\ IntersectBottom S /\ IntersectTop S /\ UnionIntersectValid S.
Class SubtypeUnionIntersectValid0 {A: Set} `(S: Subtype A) `{V: IsValidType A, E: EqvType A} `{T: Top A} `{B: Bottom A}: Prop := subtype_union_intersect_valid0: SubtypeValid0 S /\ UnionIntersectValid0 S.
Set Implicit Arguments.

(* The union properties are actually implied by subtype properties *)
Global Instance UnionTop_S {A: Set} `{S: Subtype A, T: Top A, ! SubtypeTop S}: UnionTop S.
Proof. split; [apply subtype_top | split; [apply subtype_top | intros; assumption]]. Qed.
Global Instance UnionBottom_S {A: Set} `{S: Subtype A, V: IsValidType A, B: Bottom A, ! SubtypeBottom S, ! SubtypeRefl S}: UnionBottom S.
Proof. split; [apply subtype_bottom | split; [apply subtype_refl | intros]; assumption]. Qed.
Global Instance IntersectTop_S {A: Set} `{S: Subtype A, T: Top A, V: IsValidType A, ! SubtypeTop S, ! SubtypeRefl S}: IntersectTop S.
Proof. split; [apply subtype_top | split; [apply subtype_refl; assumption | intros; assumption]]. Qed.
Global Instance IntersectBottom_S {A: Set} `{S: Subtype A, B: Bottom A, ! SubtypeBottom S}: IntersectBottom S.
Proof. split; [apply subtype_bottom | split; [apply subtype_bottom | intros]; assumption]. Qed.
Global Instance UnionRefl_S {A: Set} `{S: Subtype A, V: IsValidType A, ! SubtypeRefl S}: UnionRefl S.
Proof. split; [apply subtype_refl | split; [apply subtype_refl | intros]]; assumption. Qed.
Global Instance IntersectRefl_S {A: Set} `{S: Subtype A, V: IsValidType A, ! SubtypeRefl S}: IntersectRefl S.
Proof. split; [apply subtype_refl | split; [apply subtype_refl | intros]]; assumption. Qed.
Global Instance UnionComm_S {A: Set} `{S: Subtype A}: UnionComm S.
Proof. split; intros; destruct H, H0; repeat split; try assumption; intros; apply H1; assumption. Qed.
Global Instance IntersectComm_S {A: Set} `{S: Subtype A}: IntersectComm S.
Proof. split; intros; destruct H, H0; repeat split; try assumption; intros; apply H1; assumption. Qed.
Global Instance UnionAssoc_S {A: Set} `{S: Subtype A, ! SubtypeTrans S}: UnionAssoc S.
Proof. split; intros H1; destruct H, H0, H1, H2, H3, H4; repeat split.
- apply subtype_trans with ab; assumption.
- apply H6; [apply subtype_trans with ab |]; assumption.
- intros; apply H7; [apply H5 |]; [| apply subtype_trans with bc ..]; assumption.
- apply H5; [| apply subtype_trans with bc]; assumption.
- apply subtype_trans with bc; assumption.
- intros; apply H7; [| apply H6]; [apply subtype_trans with ab .. |]; assumption.
Qed.
Global Instance IntersectAssoc_S {A: Set} `{S: Subtype A, ! SubtypeTrans S}: IntersectAssoc S.
Proof. split; intros H1; destruct H, H0, H1; destruct H2, H3, H4; repeat split.
- apply subtype_trans with ab; assumption.
- apply H6; [apply subtype_trans with ab |]; assumption.
- intros; apply H7; [apply H5 |]; [| apply subtype_trans with bc ..]; assumption.
- apply H5; [| apply subtype_trans with bc]; assumption.
- apply subtype_trans with bc; assumption.
- intros; apply H7; [| apply H6]; [apply subtype_trans with ab .. |]; assumption.
Qed.
Global Instance UnionAbsorb_S {A: Set} `{S: Subtype A, V: IsValidType A, ! SubtypeRefl S}: UnionAbsorb S.
Proof. split; [| split; [apply subtype_refl | intros]]; assumption. Qed.
Global Instance IntersectAbsorb_S {A: Set} `{S: Subtype A, V: IsValidType A, ! SubtypeRefl S}: IntersectAbsorb S.
Proof. split; [apply subtype_refl | split; [| intros]]; assumption. Qed.
Global Instance UnionIntersectValid_S {A: Set} `{S: Subtype A, V: IsValidType A, ! SubtypeRefl S, ! SubtypeTrans S}: UnionIntersectValid S.
Proof. do 7 [> .. | split]; typeclasses eauto. Qed.
Global Instance UnionIntersectValid0_S {A: Set} `{S: Subtype A, V: IsValidType A, T: Top A, B: Bottom A, ! SubtypeTop S, ! SubtypeBottom S, ! SubtypeRefl S, ! SubtypeTrans S}: UnionIntersectValid0 S.
Proof. do 11 [> .. | split]; typeclasses eauto. Qed.
Global Instance SubtypeUnionIntersectValid0_S {A: Set} `{S: Subtype A, V: IsValidType A, E: EqvType A, T: Top A, B: Bottom A, ! SubtypeValid0 S}: SubtypeUnionIntersectValid0 S.
Proof. split; [assumption | destruct SubtypeValid1, H0, H1, H2; apply UnionIntersectValid0_S]. Qed.


(* Subtype relation implementations *)
Inductive S_option {A: Set} (S: Subtype A): Subtype (option A) :=
| S_None            : forall (lhs: option A), [S_option S] lhs <: None
| S_Some            : forall (lhs rhs: A), [S] lhs <: rhs -> [S_option S] Some lhs <: Some rhs
. Global Existing Instance S_option.
Inductive E_option {A: Set} (E: EqvType A) : EqvType (option A) :=
| E_None            : forall (lhs: option A), [E_option E] lhs == None
| E_Some            : forall (lhs rhs: A), [E] lhs == rhs -> [E_option E] (Some lhs) == (Some rhs)
. Global Existing Instance E_option.
Inductive S_Zip {A: Set} (S: Subtype A): Subtype (list A) :=
| S_Zip_nil          : forall (lhs: list A), [S_Zip S] lhs <: nil
| S_Zip_cons         : forall (l r: A) (ls rs: list A),
    [S] l <: r -> [S_Zip S] ls <: rs -> [S_Zip S] (l :: ls) <: (r :: rs)
.
Inductive E_Zip {A: Set} (E: EqvType A) : EqvType (list A) :=
| E_Zip_nil          : [E_Zip E] nil == nil
| E_Zip_cons         : forall (l r: A) (ls rs: list A),
    [E] l == r -> [E_Zip E] ls == rs -> [E_Zip E] (l :: ls) == (r :: rs)
. Global Existing Instance E_Zip.
Global Instance S_JsrZip {A: Set} (S: Subtype A): Subtype (js_record A) := JsRecord1Rel S.
Global Instance E_JsrZip {A: Set} (E: EqvType A): EqvType (js_record A) := JsRecordRel E.
Inductive S_Intersect {A: Set} (S: Subtype A): Subtype (list A) :=
| S_Intersect_nil    : forall (lhs: list A), [S_Intersect S] lhs <: nil
| S_Intersect_cons   : forall (l r: A) (ls rs: list A),
    [S] l <: r -> [S_Intersect S] ls <: rs -> [S_Intersect S] (l :: ls) <: (r :: rs)
| S_Intersect_cons_l : forall (l: A) (ls rs: list A),
                 [S_Intersect S] ls <: rs -> [S_Intersect S] (l :: ls) <: rs
.
Inductive S_variance: Subtype variance :=
| S_Bivariant        : forall (lhs: variance), [S_variance] lhs <: Bivariant
| S_Covariant        : [S_variance] Covariant <: Covariant
| S_Contravariant    : [S_variance] Contravariant <: Contravariant
| S_Invariant        : forall (rhs: variance), [S_variance] Invariant <: rhs
. Global Existing Instance S_variance.
Global Instance E_variance: EqvType variance := eq.
Inductive S_otype {A: Set} (S: Subtype A): Subtype (otype A) :=
| S_OType            : forall (ol or: bool) (lhs rhs: A), ol <= or -> [S] lhs <: rhs -> [S_otype S] Ot ol lhs <: Ot or rhs
. Global Existing Instance S_otype.
Inductive E_otype {A: Set} (E: EqvType A): EqvType (otype A) :=
| E_OType            : forall (o: bool) (lhs rhs: A), [E] lhs == rhs -> [E_otype E] Ot o lhs == Ot o rhs
. Global Existing Instance E_otype.
Inductive S_vtype {A: Set} (S: Subtype A): Subtype (vtype A) :=
| S_Void             : [S_vtype S] @VVoid A <: VVoid
| S_NotVoid          : forall (lhs rhs: A), [S] lhs <: rhs -> [S_vtype S] Vt lhs <: Vt rhs
. Global Existing Instance S_vtype.
Inductive E_vtype {A: Set} (E: EqvType A): EqvType (vtype A) :=
| E_Void             : [E_vtype E] @VVoid A == VVoid
| E_NotVoid          : forall (lhs rhs: A), [E] lhs == rhs -> [E_vtype E] Vt lhs == Vt rhs
. Global Existing Instance E_vtype.
Inductive S_tparam {A: Set} (S: Subtype A): Subtype (tparam A) :=
| S_TParam           : forall (vl vr: variance) (name: string) (supl supr: list A),
    [S_variance] vl <: vr -> [S_Intersect S] supl <: supr ->
    [S_tparam S] TParam vl name supl <: TParam vr name supr
. Global Existing Instance S_tparam.
Inductive E_tparam {A: Set} (E: EqvType A): EqvType (tparam A) :=
| E_TParam           : forall (v: variance) (name: string) (supl supr: list A),
    [E_Zip E] supl == supr -> [E_tparam E] TParam v name supl == TParam v name supr
. Global Existing Instance E_tparam.
Inductive S_itype {A: Set} (S: Subtype A): Subtype (itype A) :=
| S_Ident            : forall (name: string) (tal tar: list A), [S_Zip S] tal <: tar -> [S_itype S] It name tal <: It name tar
. Global Existing Instance S_itype.
Inductive E_itype {A: Set} (E: EqvType A): EqvType (itype A) :=
| E_Ident            : forall (name: string) (tal tar: list A), [E_Zip E] tal == tar -> [E_itype E] It name tal == It name tar
. Global Existing Instance E_itype.
Inductive S_stype {A: Set} (S: Subtype A): Subtype (stype A) :=
| S_Fn               : forall (tpl tpr: list (tparam A)) (thispl thispr: A)
                         (pl pr: list (otype A)) (rl rr: A) (retl retr: (vtype A)),
    [S_Zip (S_tparam S)] tpl :> tpr -> [S] thispl :> thispr -> [S_Zip (S_otype S)] pl :> pr -> [S] rl :> rr -> [S_vtype S] retl <: retr ->
    [S_stype S] SFn tpl thispl pl rl retl <: SFn tpr thispr pr rr retr
| S_Array            : forall (el er: A),                     [S]                     el <: er  -> [S_stype S] SArray el   <: SArray er
| S_Tuple            : forall (esl esr: list (otype A)),      [S_Zip (S_otype S)]    esl <: esr -> [S_stype S] STuple esl  <: STuple esr
| S_Object           : forall (fsl fsr: js_record (otype A)), [S_JsrZip (S_otype S)] fsl <: fsr -> [S_stype S] SObject fsl <: SObject fsr
. Global Existing Instance S_stype.
Inductive E_stype {A: Set} (E: EqvType A): EqvType (stype A) :=
| E_Fn               : forall (tpl tpr: list (tparam A)) (thispl thispr: A)
                         (pl pr: list (otype A)) (rl rr: A) (retl retr: (vtype A)),
    [E_Zip (E_tparam E)] tpl == tpr -> [E] thispl == thispr -> [E_Zip (E_otype E)] pl == pr -> [E] rl == rr -> [E_vtype E] retl == retr ->
    [E_stype E] SFn tpl thispl pl rl retl == SFn tpr thispr pr rr retr
| E_Array            : forall (el er: A),                     [E]                     el == er  -> [E_stype E] SArray el   == SArray er
| E_Tuple            : forall (esl esr: list (otype A)),      [E_Zip (E_otype E)]    esl == esr -> [E_stype E] STuple esl  == STuple esr
| E_Object           : forall (fsl fsr: js_record (otype A)), [JsRecordRel (E_otype E)] fsl == fsr -> [E_stype E] SObject fsl == SObject fsr
. Global Existing Instance E_stype.
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
. Global Existing Instance S_ftype.
Inductive E_ftype: EqvType ftype :=
| E_Any              : [E_ftype] FAny == FAny
| E_NeverNull        : forall (n: bool), [E_ftype] FNever n == FNever n
| E_Struct           : forall (n: bool) (sl sr: sftype),
    [E_stype E_ftype] sl == sr -> [E_ftype] FStructural n sl == FStructural n sr
| E_Nom              : forall (n: bool) (idl idr: iftype) (idsl idsr: list iftype) (sl sr: option sftype),
    [E_Zip (E_itype E_ftype)] (idl :: idsl) == (idr :: idsr) -> [E_option (E_stype E_ftype)] sl == sr ->
    [E_ftype] FNominal n idl idsl sl == FNominal n idr idsr sr
. Global Existing Instance E_ftype.
(* `ftype`` relations without inductive arguments AKA hypotheses, for alternate `S_ftype_ind`s *)
Inductive S_ftype0: Subtype ftype :=
| S_Any0             : forall (lhs: ftype), [S_ftype0] lhs <: FAny
| S_Never0           : forall (rhs: ftype), [S_ftype0] FNEVER <: rhs
| S_Null0            : forall (rhs: ftype), IsNullable rhs -> [S_ftype0] FNULL <: rhs
| S_Struct0          : forall (nl nr: bool) (sl sr: sftype),
    nl <= nr -> [S_ftype0] FStructural nl sl <: FStructural nr sr
| S_NomStruct0       : forall (nl nr: bool) (idl: iftype) (idsl: list iftype) (sl sr: sftype),
    nl <= nr -> [S_ftype0] FNominal nl idl idsl (Some sl) <: FStructural nr sr
| S_Nom0             : forall (nl nr: bool) (idl idr: iftype) (idsl idsr: list iftype) (sl sr: option sftype),
    nl <= nr -> [S_option (fun _ _ => True)] sl <: sr -> [S_ftype0] FNominal nl idl idsl sl <: FNominal nr idr idsr sr
. Global Existing Instance S_ftype0.
Inductive E_ftype0: EqvType ftype :=
| E_Any0             : [E_ftype0] FAny == FAny
| E_NeverNull0       : forall (n: bool), [E_ftype0] FNever n == FNever n
| E_Struct0          : forall (n: bool) (sl sr: sftype), [E_ftype0] FStructural n sl == FStructural n sr
| E_Nom0             : forall (n: bool) (idl idr: iftype) (idsl idsr: list iftype) (sl sr: option sftype), [E_ftype0] FNominal n idl idsl sl == FNominal n idr idsr sr
. Global Existing Instance E_ftype0.

Global Instance Top_option {A: Set} `{_Top: Top A}: Top (option A) := None.
Global Instance Bottom_option {A: Set} `{_Bottom: Bottom A}: Bottom (option A) := Some bottom.
Global Instance Top_variance: Top variance := Bivariant.
Global Instance Bottom_variance: Bottom variance := Invariant.
Global Instance Top_otype {A: Set} `{_Top: Top A}: Top (otype A) := Ot true _Top.
Global Instance Bottom_otype {A: Set} `{_Bottom: Bottom A}: Bottom (otype A) := Ot false _Bottom.
Global Instance Top_ftype: Top ftype := FAny.
Global Instance Bottom_ftype: Bottom ftype := FNEVER.

Global Instance IsValidType_option {A: Set} `{V: IsValidType A}: IsValidType (option A) := Option_Forall V.
Global Instance IsValidType_list {A: Set} `{V: IsValidType A}: IsValidType (list A) := List.Forall V.
Global Instance IsValidType_js_record {A: Set} `{V: IsValidType A}: IsValidType (js_record A) := JsRecordNoDupForall V.
Global Instance IsValidType_variance: IsValidType variance := IsValidType_always.
Global Instance IsValidType_otype {A: Set} `{V: IsValidType A}: IsValidType (otype A) := OType_Forall V.
Global Instance IsValidType_vtype {A: Set} `{V: IsValidType A}: IsValidType (vtype A) := VType_Forall V.
Global Instance IsValidType_tparam {A: Set} `{V: IsValidType A}: IsValidType (tparam A) := TParam_Forall V.
Global Instance IsValidType_itype {A: Set} `{V: IsValidType A}: IsValidType (itype A) := IType_Forall V.
Global Instance IsValidType_stype {A: Set} `{V: IsValidType A}: IsValidType (stype A) := SType_Forall' V.
Inductive IsValidType_ftype: IsValidType ftype :=
| FAny: IsValidType_ftype FAny
| FNever: forall x, IsValidType_ftype (FNever x)
| FStructural: forall x structure, @IsValidType_stype ftype IsValidType_ftype structure -> IsValidType_ftype (FStructural x structure)
| FNominal: forall x id sids structure, @IsValidType_itype ftype IsValidType_ftype id -> @IsValidType_list iftype (@IsValidType_itype ftype IsValidType_ftype) sids -> @IsValidType_option sftype (@IsValidType_stype ftype IsValidType_ftype) structure -> IsValidType_ftype (FNominal x id sids structure)
. Global Existing Instance IsValidType_ftype.

(* Axioms to induct on S_ftype without having to handle the complex recursion *)
Axiom S_ftype_ind_S:
  forall (P: forall {A: Set}, Subtype A -> Prop)
    (f_option: forall {A: Set} {S: Subtype A}, P S -> P (S_option S))
    (f_Zip: forall {A: Set} {S: Subtype A}, P S -> P (S_Zip S))
    (f_Intersect: forall {A: Set} {S: Subtype A}, P S -> P (S_Intersect S))
    (f_vtype: forall {A: Set} {S: Subtype A}, P S -> P (S_vtype S))
    (f_otype: forall {A: Set} {S: Subtype A}, P S -> P (S_otype S))
    (f_tparam: forall {A: Set} {S: Subtype A}, P S -> P (S_tparam S))
    (f_itype: forall {A: Set} {S: Subtype A}, P S -> P (S_itype S))
    (f_stype: forall {A: Set} {S: Subtype A}, P S -> P (S_stype S))
    (f_variance: P S_variance),
    P S_ftype0 -> P S_ftype.
Axiom S_ftype_ind_SV:
  forall (P: forall {A: Set} {V: IsValidType A}, Subtype A -> Prop)
    (f_option: forall {A: Set} {S: Subtype A} {V: IsValidType A}, P S -> P (S_option S))
    (f_Zip: forall {A: Set} {S: Subtype A} {V: IsValidType A}, P S -> P (S_Zip S))
    (f_Intersect: forall {A: Set} {S: Subtype A} {V: IsValidType A}, P S -> P (S_Intersect S))
    (f_vtype: forall {A: Set} {S: Subtype A} {V: IsValidType A}, P S -> P (S_vtype S))
    (f_otype: forall {A: Set} {S: Subtype A} {V: IsValidType A}, P S -> P (S_otype S))
    (f_tparam: forall {A: Set} {S: Subtype A} {V: IsValidType A}, P S -> P (S_tparam S))
    (f_itype: forall {A: Set} {S: Subtype A} {V: IsValidType A}, P S -> P (S_itype S))
    (f_stype: forall {A: Set} {S: Subtype A} {V: IsValidType A}, P S -> P (S_stype S))
    (f_variance: P S_variance),
    P S_ftype0 -> P S_ftype.
Axiom S_ftype_ind_SE:
  forall (P: forall {A: Set} {E: EqvType A}, Subtype A -> Prop)
    (f_option: forall {A: Set} {S: Subtype A} {E: EqvType A}, P S -> P (S_option S))
    (f_Zip: forall {A: Set} {S: Subtype A} {E: EqvType A}, P S -> P (S_Zip S))
    (f_Intersect: forall {A: Set} {S: Subtype A} {E: EqvType A}, P S -> P (S_Intersect S))
    (f_vtype: forall {A: Set} {S: Subtype A} {E: EqvType A}, P S -> P (S_vtype S))
    (f_otype: forall {A: Set} {S: Subtype A} {E: EqvType A}, P S -> P (S_otype S))
    (f_tparam: forall {A: Set} {S: Subtype A} {E: EqvType A}, P S -> P (S_tparam S))
    (f_itype: forall {A: Set} {S: Subtype A} {E: EqvType A}, P S -> P (S_itype S))
    (f_stype: forall {A: Set} {S: Subtype A} {E: EqvType A}, P S -> P (S_stype S))
    (f_variance: P S_variance),
    P S_ftype0 -> P S_ftype.
Axiom S_ftype_ind_SVE:
  forall (P: forall {A: Set} {V: IsValidType A} {E: EqvType A}, Subtype A -> Prop)
    (f_option: forall {A: Set} {S: Subtype A} {V: IsValidType A} {E: EqvType A}, P S -> P (S_option S))
    (f_Zip: forall {A: Set} {S: Subtype A} {V: IsValidType A} {E: EqvType A}, P S -> P (S_Zip S))
    (f_Intersect: forall {A: Set} {S: Subtype A} {V: IsValidType A} {E: EqvType A}, P S -> P (S_Intersect S))
    (f_vtype: forall {A: Set} {S: Subtype A} {V: IsValidType A} {E: EqvType A}, P S -> P (S_vtype S))
    (f_otype: forall {A: Set} {S: Subtype A} {V: IsValidType A} {E: EqvType A}, P S -> P (S_otype S))
    (f_tparam: forall {A: Set} {S: Subtype A} {V: IsValidType A} {E: EqvType A}, P S -> P (S_tparam S))
    (f_itype: forall {A: Set} {S: Subtype A} {V: IsValidType A} {E: EqvType A}, P S -> P (S_itype S))
    (f_stype: forall {A: Set} {S: Subtype A} {V: IsValidType A} {E: EqvType A}, P S -> P (S_stype S))
    (f_variance: P S_variance),
    P S_ftype0 -> P S_ftype.

(* Now we prove that these relations are valid *)
Global Instance SubtypeRefl_option {A: Set} `(R: SubtypeRefl A): SubtypeRefl (S_option subtype).
Proof. intros a; destruct a; constructor; apply subtype_refl; inv H; assumption. Qed.
Global Instance SubtypeAntisym_option {A: Set} `(SA: SubtypeAntisym A): SubtypeAntisym (S_option subtype).
Proof. intros a b H H0; destruct a, b; inv H H0; constructor; apply subtype_antisym; assumption. Qed.
Global Instance SubtypeTrans_option {A: Set} `{T: SubtypeTrans A}: SubtypeTrans (S_option subtype).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; apply subtype_trans with a0; assumption. Qed.

Global Instance SubtypeRefl_Zip {A: Set} `{R: SubtypeRefl A}: SubtypeRefl (S_Zip subtype).
Proof. intros a; induction a; constructor; [apply subtype_refl | apply IHa]; inv H; assumption. Qed.
Global Instance SubtypeAntisym_Zip {A: Set} `{SA: SubtypeAntisym A}: SubtypeAntisym (S_Zip subtype).
Proof. intros a b H H0; (induction2 a b using ind_list2); [inv H H0 | inv H0 H1 .. ]; constructor; [apply subtype_antisym | apply H]; assumption. Qed.
Global Instance SubtypeTrans_Zip {A: Set} `{T: SubtypeTrans A}: SubtypeTrans (S_Zip subtype).
Proof. intros a b c H H0; (induction3 a b c using ind_list3); [inv H H0 | inv H0 H1 ..]; constructor; [apply subtype_trans with y | apply H]; assumption. Qed.

Global Instance SubtypeRefl_JsrZip {A: Set} `{R: SubtypeRefl A}: SubtypeRefl (S_JsrZip subtype).
Proof. intros a; induction a; [constructor; constructor |]; destruct a as [ka va]; intros; apply JsRecord1Rel_cons with va a0; [apply subtype_refl | apply IHa | apply JsRecordAdd_head |]; inv H; assumption. Qed.
Global Instance SubtypeAntisym_JsrZip {A: Set} `{SA: SubtypeAntisym A}: SubtypeAntisym (S_JsrZip subtype).
Proof.
  intros a b H H0; pose (JsRecord1Rel_In H); pose (JsRecord1Rel_In H0); apply JsRecordRel_In0; try assumption.
  - eapply proj1, JsRecord1Rel_NoDup; exact H.
  - eapply proj1, JsRecord1Rel_NoDup; exact H0.
  - split; intros; [apply (@JsRecord1Rel_HasKey A S0) with a | apply (@JsRecord1Rel_HasKey A S0) with b]; assumption.
  - intros; apply subtype_antisym; [apply s with k | apply s0 with k]; assumption.
Qed.
Global Instance SubtypeTrans_JsrZip {A: Set} `{T: SubtypeTrans A}: SubtypeTrans (S_JsrZip subtype).
Proof.
  intros a b c H H0; pose (JsRecord1Rel_In H); pose (JsRecord1Rel_In H0); apply JsRecord1Rel_In0; try assumption.
  - eapply proj1, JsRecord1Rel_NoDup; exact H.
  - eapply proj2, JsRecord1Rel_NoDup; exact H0.
  - intros; apply (@JsRecord1Rel_HasKey A S0) with b, (@JsRecord1Rel_HasKey A S0) with c; assumption.
  - intros; destruct (JsRecordHasKey_dec k b); [| contradict H3; apply (@JsRecord1Rel_HasKey A S0) with c; [| apply JsRecordHasKey_In0 with vy]; assumption]; rewrite JsRecordHasKey_In in H3; destruct H3 as [vb H3].
    apply subtype_trans with vb; [apply s with k | apply s0 with k]; assumption.
Qed.

Lemma S_Intersect_length {A: Set} {S: Subtype A}: forall (xs ys: list A), [S_Intersect S] xs <: ys -> (List.length ys <= List.length xs)%nat.
Proof. induction 1; simpl; [apply Nat.le_0_l | rewrite <- Nat.succ_le_mono | apply Nat.le_le_succ_r]; exact IHS_Intersect. Qed.
Lemma S_Intersect_length_antisym {A: Set} {S: Subtype A}: forall (xs ys: list A), [S_Intersect S] xs <: ys -> [S_Intersect S] ys <: xs -> (List.length xs = List.length ys)%nat.
Proof. intros; apply Nat.le_antisymm; apply S_Intersect_length; assumption. Qed.
Local Ltac discr_on_intersect_length := lazymatch goal with | H: [S_Intersect _] _ <: _, H0: [S_Intersect _] _ <: _ |- _ => let e := fresh "e" in let e0 := fresh "e0" in pose' (S_Intersect_length H) as e; pose' (S_Intersect_length H0) as e0; simpl in e, e0 end; lia.

Global Instance SubtypeRefl_Intersect {A: Set} `{R: SubtypeRefl A}: SubtypeRefl (S_Intersect subtype).
Proof. intros a; induction a; constructor; [apply subtype_refl | apply IHa]; inv H; assumption. Qed.
Global Instance SubtypeAntisym_Intersect {A: Set} `{SA: SubtypeAntisym A}: SubtypeAntisym (S_Intersect subtype).
Proof.
  intros a b H H0; pose' (S_Intersect_length_antisym H H0); (induction2 a b using ind_list2); simpl in e;
    [constructor | discriminate e | discriminate e |]; inv e H0 H1; try discr_on_intersect_length;
    constructor; [apply subtype_antisym | apply H]; assumption.
Qed.
Global Instance SubtypeTrans_Intersect {A: Set} `{T: SubtypeTrans A}: SubtypeTrans (S_Intersect subtype).
Proof.
  intros a; induction a; try rename a into a0, a0 into a; induction b; try rename a1 into b0; induction c; try rename a1 into c0; intros;
    try (inv H H0; fail); [constructor .. |]; inv H H0;
    [constructor; [apply subtype_trans with b0 | apply IHa with b] | apply IHb; [constructor |] | constructor; apply IHa with (b0 :: b); [| constructor] ..]; assumption.
Qed.

Global Instance SubtypeRefl_variance: SubtypeRefl S_variance.
Proof. intros a; destruct a; constructor. Qed.
Global Instance SubtypeAntisym_variance: SubtypeAntisym S_variance.
Proof. intros a b H H0; destruct a, b; inv H H0; constructor. Qed.
Global Instance SubtypeTrans_variance: SubtypeTrans S_variance.
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor. Qed.

Global Instance SubtypeRefl_otype {A: Set} `{R: SubtypeRefl A}: SubtypeRefl (S_otype subtype).
Proof. intros a; destruct a; constructor; [destruct optional; simpl; reflexivity | apply subtype_refl]; inv H; assumption. Qed.
Global Instance SubtypeAntisym_otype {A: Set} `{SA: SubtypeAntisym A}: SubtypeAntisym (S_otype subtype).
Proof. intros a b H H0; destruct a, b; inv H H0; destruct optional, optional0; try discriminate; constructor; apply subtype_antisym; assumption. Qed.
Global Instance SubtypeTrans_otype {A: Set} `{T: SubtypeTrans A}: SubtypeTrans (S_otype subtype).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; destruct optional, optional0, optional1; try discriminate; constructor; (simpl; reflexivity) || apply subtype_trans with a0; assumption. Qed.

Global Instance SubtypeRefl_vtype {A: Set} `{R: SubtypeRefl A}: SubtypeRefl (S_vtype subtype).
Proof. intros a; destruct a; constructor; apply subtype_refl; inv H; assumption. Qed.
Global Instance SubtypeAntisym_vtype {A: Set} `{SA: SubtypeAntisym A}: SubtypeAntisym (S_vtype subtype).
Proof. intros a b H H0; destruct a, b; inv H H0; constructor; apply subtype_antisym; assumption. Qed.
Global Instance SubtypeTrans_vtype {A: Set} `{T: SubtypeTrans A}: SubtypeTrans (S_vtype subtype).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; apply subtype_trans with a0; assumption. Qed.

Global Instance SubtypeRefl_tparam {A: Set} `{R: SubtypeRefl A}: SubtypeRefl (S_tparam subtype).
Proof. intros a; destruct a; constructor; apply subtype_refl; [reflexivity | inv H; assumption]. Qed.
Global Instance SubtypeAntisym_tparam {A: Set} `{SA: SubtypeAntisym A}: SubtypeAntisym (S_tparam subtype).
Proof. intros a b H H0; destruct a, b; inv H H0; rewrite (SubtypeAntisym_variance H2 H3); constructor; apply SubtypeAntisym_Intersect; assumption. Qed.
Global Instance SubtypeTrans_tparam {A: Set} `{T: SubtypeTrans A}: SubtypeTrans (S_tparam subtype).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; [apply subtype_trans with v0 | apply subtype_trans with supers0]; assumption. Qed.

Global Instance SubtypeRefl_itype {A: Set} `{R: SubtypeRefl A}: SubtypeRefl (S_itype subtype).
Proof. intros a; destruct a; constructor; apply subtype_refl; inv H; assumption. Qed.
Global Instance SubtypeAntisym_itype {A: Set} `{SA: SubtypeAntisym A}: SubtypeAntisym (S_itype subtype).
Proof. intros a b H H0; destruct a, b; inv H H0; constructor; apply SubtypeAntisym_Zip; assumption. Qed.
Global Instance SubtypeTrans_itype {A: Set} `{T: SubtypeTrans A}: SubtypeTrans (S_itype subtype).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; apply subtype_trans with targs0; assumption. Qed.

Global Instance SubtypeRefl_stype: forall {A: Set} `{R: SubtypeRefl A}, SubtypeRefl (S_stype subtype).
Proof. intros A S0 V S a; destruct a; constructor; apply subtype_refl; inv H; assumption. Qed.
Global Instance SubtypeAntisym_stype {A: Set} `{SA: SubtypeAntisym A}: SubtypeAntisym (S_stype subtype).
Proof. intros a b H H0; destruct a, b; inv H H0; constructor; apply subtype_antisym || apply SubtypeAntisym_Zip; assumption. Qed.
Global Instance SubtypeTrans_stype {A: Set} `{T: SubtypeTrans A}: SubtypeTrans (S_stype subtype).
Proof. intros a b c H H0; destruct a, b, c; inv H H0; constructor; eapply subtype_trans; eassumption. Qed.

Global Instance SubtypeTop_ftype: SubtypeTop S_ftype.
Proof. constructor. Qed.
Global Instance SubtypeBottom_ftype: SubtypeBottom S_ftype.
Proof. constructor. Qed.
Global Instance SubtypeRefl_ftype: SubtypeRefl S_ftype.
Proof. apply S_ftype_ind_SV; [typeclasses eauto; fail .. |]. intros a; destruct a; intros; [constructor | destruct nullable; constructor; reflexivity | constructor; destruct nullable; reflexivity | constructor; [destruct nullable; reflexivity | destruct structure; constructor; constructor]]. Qed.
Global Instance SubtypeAntisym_ftype: SubtypeAntisym S_ftype.
Proof. apply S_ftype_ind_SE; [typeclasses eauto; fail .. |]. intros a b; destruct a, b; intros; inv H H0; [constructor | constructor | inv H1 | inv H2 | constructor | destruct nullable, nullable0; inv H1 H2; constructor | destruct nullable, nullable0, structure, structure0; inv H2 H3 H10 H11; constructor]. Qed.
Global Instance SubtypeTrans_ftype: SubtypeTrans S_ftype.
Proof. apply S_ftype_ind_S; [typeclasses eauto; fail .. |]. intros a b c; destruct a, b, c; intros; inv H H0; try destruct nullable; try destruct nullable0; try destruct nullable1; try destruct structure; try destruct structure0; try destruct structure1; try constructor; try reflexivity; try discr_inv; try constructor; try constructor. Qed.
Global Instance SubtypeValid_ftype: SubtypeValid S_ftype.
Proof. repeat split; typeclasses eauto. Qed.
Global Instance SubtypeValid0_ftype: SubtypeValid0 S_ftype.
Proof. repeat split; typeclasses eauto. Qed.
Global Instance SubtypeUnionIntersectValid0_ftype: SubtypeUnionIntersectValid0 S_ftype.
Proof. typeclasses eauto. Qed.

Corollary union_subtype_lattice0 {A: Set} `{S: Subtype A, V: IsValidType A, E: EqvType A, ! SubtypeValid S}: forall (a b ab c: A), a <: c -> b <: c -> a U b = ab -> ab <: c.
Proof. intros; destruct H1, H2; apply H3; assumption. Qed.
Corollary intersect_subtype_lattice0 {A: Set} `{S: Subtype A, V: IsValidType A, E: EqvType A, ! SubtypeValid S}: forall (a b ab c: A), c <: a -> c <: b -> a I b = ab -> c <: ab.
Proof. intros; destruct H1, H2; apply H3; assumption. Qed.
Corollary union_subtype_lattice1 {A: Set} `{S: Subtype A, V: IsValidType A, E: EqvType A, ! SubtypeValid S}: forall (a b c d ab cd: A), a <: c -> b <: d -> a U b = ab -> c U d = cd -> ab <: cd.
Proof. intros; destruct H1, H2, H3, H4, SubtypeValid1, H8; apply H5; [apply subtype_trans with c | apply subtype_trans with d]; assumption. Qed.
Corollary intersect_subtype_lattice1 {A: Set} `{S: Subtype A, V: IsValidType A, E: EqvType A, ! SubtypeValid S}: forall (a b c d ab cd: A), a <: c -> b <: d -> a I b = ab -> c I d = cd -> ab <: cd.
Proof. intros; destruct H1, H2, H3, H4, SubtypeValid1, H8; apply H6; [apply subtype_trans with a | apply subtype_trans with b]; assumption. Qed.
Corollary union_subtype_lattice2 {A: Set} `{S: Subtype A, V: IsValidType A, E: EqvType A, ! SubtypeValid S}: forall (a b ab: A), a U b = ab -> a <: ab /\ b <: ab.
Proof. intros; destruct H, H0; split; assumption. Qed.
Corollary intersect_subtype_lattice2 {A: Set} `{S: Subtype A, V: IsValidType A, E: EqvType A, ! SubtypeValid S}: forall (a b ab: A), a I b = ab -> ab <: a /\ ab <: b.
Proof. intros; destruct H, H0; split; assumption. Qed.


Create HintDb subtype_laws.
Global Hint Extern 4 => typeclasses eauto: subtype_laws.
Global Hint Resolve subtype_top: subtype_laws.
Global Hint Resolve subtype_bottom: subtype_laws.
Global Hint Resolve subtype_refl: subtype_laws.
Global Hint Resolve subtype_antisym: subtype_laws.
Global Hint Resolve subtype_trans: subtype_laws.
Global Hint Resolve union_top: subtype_laws.
Global Hint Resolve union_bottom: subtype_laws.
Global Hint Resolve union_refl: subtype_laws.
Global Hint Resolve union_comm: subtype_laws.
Global Hint Resolve union_assoc: subtype_laws.
Global Hint Resolve union_absorb: subtype_laws.
Global Hint Resolve intersect_top: subtype_laws.
Global Hint Resolve intersect_bottom: subtype_laws.
Global Hint Resolve intersect_refl: subtype_laws.
Global Hint Resolve intersect_comm: subtype_laws.
Global Hint Resolve intersect_assoc: subtype_laws.
Global Hint Resolve intersect_absorb: subtype_laws.
Global Hint Resolve union_subtype_lattice0: subtype_laws.
Global Hint Resolve intersect_subtype_lattice0: subtype_laws.
Global Hint Resolve union_subtype_lattice1: subtype_laws.
Global Hint Resolve intersect_subtype_lattice1: subtype_laws.
Global Hint Resolve union_subtype_lattice2: subtype_laws.
Global Hint Resolve intersect_subtype_lattice2: subtype_laws.
