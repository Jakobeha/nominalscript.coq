(* -*- company-coq-local-symbols: (("U" . ?∪) ("I" . ?∩)); -*- *)
(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Program.Equality.
From NS Require Import Misc.
From NS Require Import JsRecord.
From NS Require Import TypesBase.
From NS Require Import TypesNotation.
From NS Require Import TypesSimpleHelpers.

Set Default Timeout 10.

Local Open Scope list_scope.
Local Notation "a <= b" := (Bool.le a b) : bool_scope.
Local Notation "a >= b" := (Bool.le b a) : bool_scope.
Definition USKind (A: Set) := A -> A -> A -> Prop.
Definition ISKind (A: Set) := A -> A -> A -> Prop.
Definition US_ap {A: Set} (US: USKind A) (a b c: A): Prop := US a b c.
Definition IS_ap {A: Set} (IS: ISKind A) (a b c: A): Prop := IS a b c.
Class USOf (A: Set) := US_ : USKind A.
Class ISOf (A: Set) := IS_ : ISKind A.
Definition CommonSupertype {A: Set} {US: USOf A} (a b c: A) : Prop := US a b c.
Definition CommonSubtype {A: Set} {IS: ISOf A} (a b c: A) : Prop := IS a b c.
Notation "'[' CS ']' a 'U' b '<:' c" := (US_ap CS a b c) (at level 60, a at next level, b at next level, no associativity).
Notation "'[' CS ']' a 'I' b ':>' c" := (IS_ap CS a b c) (at level 60, a at next level, b at next level, no associativity).
Notation "a 'U' b '<:' c" := (CommonSupertype a b c) (at level 60, b at next level, no associativity).
Notation "a 'I' b ':>' c" := (CommonSubtype a b c) (at level 60, b at next level, no associativity).
(* with CommonSupertype_opt : option A -> option A -> option A -> Prop := *)
Inductive US_option {A: Set} (US: USKind A) : USKind (option A) :=
| US_None            : forall (lhs rhs: option A), [US_option US] lhs U rhs <: None
| US_Some            : forall (lhs rhs uni: A), [US] lhs U rhs <: uni -> [US_option US] Some lhs U Some rhs <: Some uni
.
Global Instance USOf_option {A: Set} {US: USOf A} : USOf (option A) := US_option US.
Inductive IS_option {A: Set} (IS: ISKind A) : ISKind (option A) :=
| IS_NoneNone        : forall (uni: option A), [IS_option IS] None I None :> uni
| IS_NoneSome        : forall (lhs: A), [IS_option IS] Some lhs I None :> Some lhs
| IS_SomeNone        : forall (rhs: A), [IS_option IS] None I Some rhs :> Some rhs
| IS_SomeSome        : forall (lhs rhs uni: A), [IS] lhs I rhs :> uni -> [IS_option IS] Some lhs I Some rhs :> Some uni
.
Global Instance ISOf_option {A: Set} {IS: ISOf A} : ISOf (option A) := IS_option IS.
Inductive US_Zip {A: Set} (US: USKind A) : USKind (list A) :=
| US_Zip_nil_r       : forall (lhs: list A), [US_Zip US] lhs U nil <: nil
| US_Zip_nil_l       : forall (rhs: list A), [US_Zip US] nil U rhs <: nil
| US_Zip_cons        : forall (l r u: A) (ls rs us: list A),
    [US] l U r <: u -> [US_Zip US] ls U rs <: us -> [US_Zip US] (l :: ls) U (r :: rs) <: (u :: us)
.
Inductive IS_Zip {A: Set} (IS: ISKind A) : ISKind (list A) :=
| IS_Zip_nil         : forall (uni: list A), [IS_Zip IS] nil I nil :> uni
| IS_Zip_cons        : forall (l r u: A) (ls rs us: list A),
    [IS] l I r :> u -> [IS_Zip IS] ls I rs :> us -> [IS_Zip IS] (l :: ls) I (r :: rs) :> (u :: us)
.
Inductive US_JsrZip {A: Set} (US: USKind A) : USKind (js_record A) :=
| US_JsrZip_nil_r    : forall (lhs: js_record A), [US_JsrZip US] lhs U nil <: lhs
| US_JsrZip_nil_l    : forall (rhs: js_record A), [US_JsrZip US] nil U rhs <: rhs
| US_JsrZip_cons_l   : forall (k: string) (vl vr vu: A) (ls rs rs' us: js_record A),
    [US] vl U vr <: vu -> [US_JsrZip US] ls U rs <: us -> JsRecordAdd k vr rs rs' -> [US_JsrZip US] ((k, vl) :: ls) U rs' <: ((k, vu) :: us)
| US_JsrZip_cons_r   : forall (k: string) (vl vr vu: A) (ls ls' rs us: js_record A),
    [US] vl U vr <: vu -> [US_JsrZip US] ls U rs <: us -> JsRecordAdd k vl ls ls' -> [US_JsrZip US] ls' U ((k, vr) :: rs) <: ((k, vu) :: us)
| US_JsrZip_cons_u   : forall (k: string) (vl vr vu: A) (ls rs us us': js_record A),
    [US] vl U vr <: vu -> [US_JsrZip US] ls U rs <: us -> JsRecordAdd k vu us us' -> [US_JsrZip US] ((k, vl) :: ls) U ((k, vr) :: rs) <: us'
.
Inductive IS_JsrZip {A: Set} (IS: ISKind A) : ISKind (js_record A) :=
| IS_JsrZip_nil      : forall (uni: js_record A), [IS_JsrZip IS] nil I nil :> uni
| IS_JsrZip_cons_l   : forall (k: string) (vl vr vu: A) (ls rs rs' us: js_record A),
    [IS] vl I vr :> vu -> [IS_JsrZip IS] ls I rs :> us -> JsRecordAdd k vr rs rs' -> [IS_JsrZip IS] ((k, vl) :: ls) I rs' :> ((k, vu) :: us)
| IS_JsrZip_cons_r   : forall (k: string) (vl vr vu: A) (ls ls' rs us: js_record A),
    [IS] vl I vr :> vu -> [IS_JsrZip IS] ls I rs :> us -> JsRecordAdd k vl ls ls' -> [IS_JsrZip IS] ls' I ((k, vr) :: rs) :> ((k, vu) :: us)
| IS_JsrZip_cons_u   : forall (k: string) (vl vr vu: A) (ls rs us us': js_record A),
    [IS] vl I vr :> vu -> [IS_JsrZip IS] ls I rs :> us -> JsRecordAdd k vu us us' -> [IS_JsrZip IS] ((k, vl) :: ls) I ((k, vr) :: rs) :> us'
.
Inductive US_Intersect {A: Set} (US: USKind A) : USKind (list A) :=
| US_Intersect_nil   : forall (uni: list A), [US_Intersect US] nil U nil <: uni
| US_Intersect_cons_l: forall (l r u: A) (ls rs rs' us: list A),
    [US] l U r <: u -> [US_Intersect US] ls U rs <: us -> List.Add r rs rs' -> [US_Intersect US] (l :: ls) U rs' <: (u :: us)
| US_Intersect_cons_r: forall (l r u: A) (ls ls' rs us: list A),
    [US] l U r <: u -> [US_Intersect US] ls U rs <: us -> List.Add l ls ls' -> [US_Intersect US] ls' U (r :: rs) <: (u :: us)
| US_Intersect_cons_u: forall (l r u: A) (ls rs us us': list A),
    [US] l U r <: u -> [US_Intersect US] ls U rs <: us -> List.Add u us us' -> [US_Intersect US] (l :: ls) U (r :: rs) <: us'
.
Inductive IS_Intersect {A: Set} (IS: ISKind A) : ISKind (list A) :=
| IS_Intersect_nil_r : forall (lhs: list A), [IS_Intersect IS] lhs I nil :> lhs
| IS_Intersect_nil_l : forall (rhs: list A), [IS_Intersect IS] nil I rhs :> rhs
| IS_Intersect_cons_l: forall (l r u: A) (ls rs rs' us: list A),
    [IS] l I r :> u -> [IS_Intersect IS] ls I rs :> us -> List.Add r rs rs' -> [IS_Intersect IS] (l :: ls) I rs' :> (u :: us)
| IS_Intersect_cons_r: forall (l r u: A) (ls ls' rs us: list A),
    [IS] l I r :> u -> [IS_Intersect IS] ls I rs :> us -> List.Add l ls ls' -> [IS_Intersect IS] ls' I (r :: rs) :> (u :: us)
| IS_Intersect_cons_u: forall (l r u: A) (ls rs us us': list A),
    [IS] l I r :> u -> [IS_Intersect IS] ls I rs :> us -> List.Add u us us' -> [IS_Intersect IS] (l :: ls) I (r :: rs) :> us'
.
Inductive US_variance : USKind variance :=
| US_Bivariant       : forall (lhs rhs: variance), [US_variance] lhs U rhs <: Bivariant
| US_Covariant       : [US_variance] Covariant U Covariant <: Covariant
| US_Contravariant   : [US_variance] Contravariant U Contravariant <: Contravariant
| US_InvariantL      : forall (rhs: variance), [US_variance] Invariant U rhs <: rhs
| US_InvariantR      : forall (lhs: variance), [US_variance] lhs U Invariant <: lhs
.
Global Instance USOf_variance : USOf variance := US_variance.
Inductive IS_variance : ISKind variance :=
| IS_Invariant       : forall (lhs rhs: variance), [IS_variance] lhs I rhs :> Invariant
| IS_Covariant       : [IS_variance] Covariant I Covariant :> Covariant
| IS_Contravariant   : [IS_variance] Contravariant I Contravariant :> Contravariant
| IS_Bivariant       : forall (a: variance), [IS_variance] Bivariant I Bivariant :> a
| IS_BivariantL      : forall (rhs: variance), [IS_variance] Bivariant I rhs :> rhs
| IS_BivariantR      : forall (lhs: variance), [IS_variance] lhs I Bivariant :> lhs
.
Global Instance ISOf_variance : ISOf variance := IS_variance.
Inductive US_otype {A: Set} (US: USKind A) : USKind (otype A) :=
| US_OType           : forall (ol or ou: bool) (lhs rhs uni: A),
    ol || or <= ou -> [US] lhs U rhs <: uni -> [US_otype US] Ot ol lhs U Ot or rhs <: Ot ou uni
.
Global Instance USOf_otype {A: Set} {US: USOf A} : USOf (otype A) := US_otype US.
Inductive IS_otype {A: Set} (IS: ISKind A) : ISKind (otype A) :=
| IS_OType           : forall (ol or ou: bool) (lhs rhs uni: A),
    ol && or >= ou -> [IS] lhs I rhs :> uni -> [IS_otype IS] Ot ol lhs I Ot or rhs :> Ot ou uni
.
Global Instance ISOf_otype {A: Set} {IS: ISOf A} : ISOf (otype A) := IS_otype IS.
Inductive US_vtype {A: Set} (US: USKind A) : USKind (vtype A) :=
| US_Void            : [US_vtype US] @VVoid A U VVoid <: VVoid
| US_NotVoid         : forall (lhs rhs uni: A), [US] lhs U rhs <: uni -> [US_vtype US] Vt lhs U Vt rhs <: Vt uni
.
Global Instance USOf_vtype {A: Set} {US: USOf A} : USOf (vtype A) := US_vtype US.
Inductive IS_vtype {A: Set} (IS: ISKind A) : ISKind (vtype A) :=
| IS_Void            : [IS_vtype IS] @VVoid A I VVoid :> VVoid
| IS_NotVoid         : forall (lhs rhs uni: A), [IS] lhs I rhs :> uni -> [IS_vtype IS] Vt lhs I Vt rhs :> Vt uni
.
Global Instance ISOf_vtype {A: Set} {IS: ISOf A} : ISOf (vtype A) := IS_vtype IS.
Inductive US_tparam {A: Set} (US: USKind A) : USKind (tparam A) :=
| US_TParam          : forall (vl vr vu: variance) (name: string) (supl supr supu: list A),
    [US_variance] vl U vr <: vu -> [US_Intersect US] supl U supr <: supu ->
    [US_tparam US] TParam vl name supl U TParam vr name supr <: TParam vu name supu
.
Global Instance USOf_tparam {A: Set} {US: USOf A} : USOf (tparam A) := US_tparam US.
Inductive IS_tparam {A: Set} (IS: ISKind A) : ISKind (tparam A) :=
| IS_TParam          : forall (vl vr vu: variance) (name: string) (supl supr supu: list A),
    [IS_variance] vl I vr :> vu -> [IS_Intersect IS] supl I supr :> supu ->
    [IS_tparam IS] TParam vl name supl I TParam vr name supr :> TParam vu name supu
.
Global Instance ISOf_tparam {A: Set} {IS: ISOf A} : ISOf (tparam A) := IS_tparam IS.
Inductive US_itype {A: Set} (US: USKind A) : USKind (itype A) :=
| US_Ident           : forall (name: string) (tal tar tau: list A), [US_Zip US] tal U tar <: tau -> [US_itype US] It name tal U It name tar <: It name tau
.
Global Instance USOf_itype {A: Set} {US: USOf A} : USOf (itype A) := US_itype US.
Inductive IS_itype {A: Set} (IS: ISKind A) : ISKind (itype A) :=
| IS_Ident           : forall (name: string) (tal tar tau: list A), [IS_Zip IS] tal I tar :> tau -> [IS_itype IS] It name tal I It name tar :> It name tau
.
Global Instance ISOf_itype {A: Set} {IS: ISOf A} : ISOf (itype A) := IS_itype IS.
Inductive US_stype {A: Set} (US: USKind A) (IS: ISKind A) : USKind (stype A) :=
| US_Fn              : forall (tpl tpr tpu: list (tparam A)) (thispl thispr thispu: A)
                         (pl pr pu: list (otype A)) (rl rr ru: A) (retl retr retu: (vtype A)),
    [IS_Zip (IS_tparam IS)] tpl I tpr :> tpu -> [IS] thispl I thispr :> thispu -> [IS_Zip (IS_otype US)] pl I pr :> pu -> [IS] rl I rr :> ru -> [US_vtype US] retl U retr <: retu ->
    [US_stype US IS] SFn tpl thispl pl rl retl U SFn tpr thispr pr rr retr <: SFn tpu thispu pu ru retu
| US_Array           : forall (el er eu: A),                      [US]                      el  U er  <: eu  -> [US_stype US IS] SArray el   U SArray er   <: SArray eu
| US_Tuple           : forall (esl esr esu: list (otype A)),      [US_Zip (US_otype US)]    esl U esr <: esu -> [US_stype US IS] STuple esl  U STuple esr  <: STuple esu
| US_Object          : forall (fsl fsr fsu: js_record (otype A)), [US_JsrZip (US_otype US)] fsl U fsr <: fsu -> [US_stype US IS] SObject fsl U SObject fsr <: SObject fsu
.
Global Instance USOf_stype {A: Set} {US: USOf A} {IS: ISOf A} : USOf (stype A) := US_stype US IS.
Inductive IS_stype {A: Set} (US: USKind A) (IS: ISKind A) : ISKind (stype A) :=
| IS_Fn              : forall (tpl tpr tpu: list (tparam A)) (thispl thispr thispu: A)
                             (pl pr pu: list (otype A)) (rl rr ru: A) (retl retr retu: vtype A),
    [US_Zip (US_tparam IS)] tpl U tpr <: tpu -> [US] thispl U thispr <: thispu -> [US_Zip (US_otype IS)] pl U pr <: pu -> [US] rl U rr <: ru -> [IS_vtype IS] retl I retr :> retu ->
    [IS_stype US IS] SFn tpl thispl pl rl retl I SFn tpr thispr pr rr retr :> SFn tpu thispu pu ru retu
| IS_Array           : forall (el er eu: A),                      [IS]                      el  I er  :> eu  -> [IS_stype US IS] SArray el   I SArray er   :> SArray eu
| IS_Tuple           : forall (esl esr esu: list (otype A)),      [IS_Zip (IS_otype IS)]    esl I esr :> esu -> [IS_stype US IS] STuple esl  I STuple esr  :> STuple esu
| IS_Object          : forall (fsl fsr fsu: js_record (otype A)), [IS_JsrZip (IS_otype IS)] fsl I fsr :> fsu -> [IS_stype US IS] SObject fsl I SObject fsr :> SObject fsu
.
Global Instance ISOf_stype {A: Set} {US: USOf A} {IS: ISOf A} : ISOf (stype A) := IS_stype US IS.
Inductive US_ftype : USKind ftype :=
| US_Any             : forall (lhs rhs: ftype), [US_ftype] lhs U rhs <: FAny
| US_Never           : forall (a: ftype), [US_ftype] FNEVER U FNEVER <: a
| US_NeverL          : forall (rhs: ftype), [US_ftype] FNEVER U rhs <: rhs
| US_NeverR          : forall (lhs: ftype), [US_ftype] lhs U FNEVER <: lhs
| US_Null            : forall (a: ftype), IsNullable a -> [US_ftype] FNULL U FNULL <: a
| US_NullL           : forall (rhs: ftype), IsNullable rhs -> [US_ftype] FNULL U rhs <: rhs
| US_NullR           : forall (lhs: ftype), IsNullable lhs -> [US_ftype] lhs U FNULL <: lhs
| US_NeverNull       : [US_ftype] FNEVER U FNEVER <: FNULL
| US_Struct          : forall (nl nr nu: bool) (sl sr su: sftype),
    nl || nr <= nu -> [US_stype US_ftype IS_ftype] sl U sr <: su -> [US_ftype] FStructural nl sl U FStructural nr sr <: FStructural nu su
| US_NomStruct       : forall (nl nr nu: bool) (idl: iftype) (idsl: list iftype) (sl sr su: sftype),
    nl || nr <= nu -> [US_stype US_ftype IS_ftype] sl U sr <: su -> [US_ftype] FNominal nl idl idsl (Some sl) U FStructural nr sr <: FStructural nu su
| US_StructNom       : forall (nl nr nu: bool) (idr: iftype) (idsr: list iftype) (sl sr su: sftype),
    nl || nr <= nu -> [US_stype US_ftype IS_ftype] sl U sr <: su -> [US_ftype] FStructural nl sl U FNominal nr idr idsr (Some sr) <: FStructural nu su
| US_NomCommonNom    : forall (nl nr nu: bool) (idl idr idu: iftype) (idsl idsr idsu: list iftype) (sl sr su: option sftype),
    nl || nr <= nu -> [US_Intersect (US_itype US_ftype)] (idl :: idsl) U (idr :: idsr) <: (idu :: idsu) -> [US_option (US_stype US_ftype IS_ftype)] sl U sr <: su ->
    [US_ftype] FNominal nl idl idsl sl U FNominal nr idr idsr sr <: FNominal nu idu idsu su
| US_NomCommonStruct : forall (nl nr nu: bool) (idl idr: iftype) (idsl idsr: list iftype) (sl sr su: sftype),
    nl || nr <= nu -> [US_stype US_ftype IS_ftype] sl U sr <: su -> [US_ftype] FNominal nl idl idsl (Some sl) U FNominal nr idr idsr (Some sr) <: FStructural nu su
with IS_ftype : ISKind ftype :=
| IS_Never           : forall (lhs rhs: ftype), [IS_ftype] lhs I rhs :> FNEVER
| IS_Null            : forall (lhs rhs: ftype), IsNullable lhs -> IsNullable rhs -> [IS_ftype] lhs I rhs :> FNULL
| IS_AnyL            : forall (rhs: ftype), [IS_ftype] FAny I rhs :> rhs
| IS_AnyR            : forall (lhs: ftype), [IS_ftype] lhs I FAny :> lhs
| IS_Struct          : forall (nl nr nu: bool) (sl sr su: sftype),
    nl && nr >= nu -> [IS_stype US_ftype IS_ftype] sl I sr :> su -> [IS_ftype] FStructural nl sl I FStructural nr sr :> FStructural nu su
| IS_NomStruct       : forall (nl nr nu: bool) (idl idu: iftype) (idsl idsu: list iftype) (sl sr su: sftype),
    nl && nr >= nu -> [IS_Intersect (IS_itype IS_ftype)] (idl :: idsl) I nil :> (idu :: idsu) -> [IS_stype US_ftype IS_ftype] sl I sr :> su ->
    [IS_ftype] FNominal nl idl idsl (Some sl) I FStructural nr sr :> FNominal nu idu idsu (Some su)
| IS_StructNom       : forall (nl nr nu: bool) (idr idu: iftype) (idsr idsu: list iftype) (sl sr su: sftype),
    nl && nr >= nu -> [IS_Intersect (IS_itype IS_ftype)] nil I (idr :: idsr) :> (idu :: idsu) -> [IS_stype US_ftype IS_ftype] sl I sr :> su ->
    [IS_ftype] FStructural nl sl I FNominal nr idr idsr (Some sr) :> FNominal nu idu idsu (Some su)
| IS_Nom             : forall (nl nr nu: bool) (idl idr idu: iftype) (idsl idsr idsu: list iftype) (sl sr su: option sftype),
    nl && nr >= nu -> [IS_Intersect (IS_itype IS_ftype)] (idl :: idsl) I (idr :: idsr) :> (idu :: idsu) -> [IS_option (IS_stype US_ftype IS_ftype)] sl I sr :> su ->
    [IS_ftype] FNominal nl idl idsl sl I FNominal nr idr idsr sr :> FNominal nu idu idsu su
.
Global Instance USOf_ftype : USOf ftype := US_ftype.
Global Instance ISOf_ftype : ISOf ftype := IS_ftype.
Axiom CS_ftype_ind':
  forall (Pu: USKind ftype) (Pi: ISKind ftype)
    (fUS_Any: forall lhs rhs: ftype, Pu lhs rhs FAny)
    (fUS_Never: forall a: ftype, Pu FNEVER FNEVER a)
    (fUS_NeverL: forall rhs : ftype, Pu FNEVER rhs rhs)
    (fUS_NeverR: forall lhs : ftype, Pu lhs FNEVER lhs)
    (fUS_Null: forall a : ftype, IsNullable a -> Pu FNULL FNULL a)
    (fUS_NullL: forall rhs : ftype, IsNullable rhs -> Pu FNULL rhs rhs)
    (fUS_NullR: forall lhs : ftype, IsNullable lhs -> Pu lhs FNULL lhs)
    (fUS_NeverNull: Pu FNEVER FNEVER FNULL)
    (fUS_Struct: forall (nl nr nu : bool) (sl sr su : sftype),
      nu >= nl || nr ->
      [US_stype Pu Pi] sl U sr <: su ->
      Pu (FStructural nl sl) (FStructural nr sr) (FStructural nu su))
    (fUS_NomStruct: forall (nl nr nu : bool) (idl : iftype) (idsl : list iftype) (sl sr su : sftype),
      nu >= nl || nr ->
      [US_stype Pu Pi] sl U sr <: su ->
      Pu (FNominal nl idl idsl (Some sl)) (FStructural nr sr) (FStructural nu su))
    (fUS_StructNom: forall (nl nr nu : bool) (idr : iftype) (idsr : list iftype) (sl sr su : sftype),
      nu >= nl || nr ->
      [US_stype Pu Pi] sl U sr <: su ->
      Pu (FStructural nl sl) (FNominal nr idr idsr (Some sr)) (FStructural nu su))
    (fUS_NomCommonNom: forall (nl nr nu : bool) (idl idr idu : iftype) (idsl idsr idsu : list iftype)
        (sl sr su : option sftype),
      nu >= nl || nr ->
      [US_Intersect (US_itype Pu)] (idl :: idsl) U (idr :: idsr) <: (idu :: idsu) ->
      [US_option (US_stype Pu Pi)] sl U sr <: su ->
      Pu (FNominal nl idl idsl sl) (FNominal nr idr idsr sr) (FNominal nu idu idsu su))
    (fUS_NomCommonStruct: forall (nl nr nu : bool) (idl idr : iftype) (idsl idsr : list iftype) (sl sr su : sftype),
      nu >= nl || nr ->
      [US_stype Pu Pi] sl U sr <: su ->
      Pu (FNominal nl idl idsl (Some sl)) (FNominal nr idr idsr (Some sr)) (FStructural nu su))
    (fIS_Never: forall lhs rhs : ftype, Pi lhs rhs FNEVER)
    (fIS_Null: forall lhs rhs : ftype, IsNullable lhs -> IsNullable rhs -> Pi lhs rhs FNULL)
    (fIS_AnyL: forall rhs : ftype, Pi FAny rhs rhs)
    (fIS_AnyR: forall lhs : ftype, Pi lhs FAny lhs)
    (fIS_Struct: forall (nl nr nu : bool) (sl sr su : sftype),
      nl && nr >= nu ->
      [IS_stype Pu Pi] sl I sr :> su ->
      Pi (FStructural nl sl) (FStructural nr sr) (FStructural nu su))
    (fIS_NomStruct: forall (nl nr nu : bool) (idl idu : iftype) (idsl idsu : list iftype) (sl sr su : sftype),
      nl && nr >= nu ->
      [IS_Intersect (IS_itype Pi)] (idl :: idsl) I nil :> (idu :: idsu) ->
      [IS_stype Pu Pi] sl I sr :> su ->
      Pi (FNominal nl idl idsl (Some sl)) (FStructural nr sr) (FNominal nu idu idsu (Some su)))
    (fIS_StructNom: forall (nl nr nu : bool) (idr idu : iftype) (idsr idsu : list iftype) (sl sr su : sftype),
      nl && nr >= nu ->
      [IS_Intersect (IS_itype Pi)] nil I (idr :: idsr) :> (idu :: idsu) ->
      [IS_stype Pu Pi] sl I sr :> su ->
      Pi (FStructural nl sl) (FNominal nr idr idsr (Some sr)) (FNominal nu idu idsu (Some su)))
    (fIS_Nom: forall (nl nr nu : bool) (idl idr idu : iftype) (idsl idsr idsu : list iftype)
      (sl sr su : option sftype),
      nl && nr >= nu ->
      [IS_Intersect (IS_itype Pi)] (idl :: idsl) I (idr :: idsr) :> (idu :: idsu) ->
      [IS_option (IS_stype Pu Pi)] sl I sr :> su ->
      Pi (FNominal nl idl idsl sl) (FNominal nr idr idsr sr) (FNominal nu idu idsu su))
    (a b c: ftype), (US_ftype a b c -> Pu a b c) /\ (IS_ftype a b c -> Pi a b c).

Inductive HasVariance {A: Set} {US: USOf A}: A -> A -> variance -> Prop :=
| IsBivariant     : forall (lhs rhs uni: A), lhs U rhs <: uni -> HasVariance lhs rhs Bivariant
| IsCovariant     : forall (lhs rhs    : A), lhs U rhs <: rhs -> HasVariance lhs rhs Covariant
| IsContravariant : forall (lhs rhs    : A), lhs U rhs <: lhs -> HasVariance lhs rhs Contravariant
| IsInvariant     : forall (a          : A), a U a <: a       -> HasVariance a   a   Invariant
.

Definition IsSubtype {A: Set} {US: USOf A} (lhs rhs: A): Prop := lhs U rhs <: rhs.
Notation "'(<:)'" := IsSubtype.
Notation "lhs '<:' rhs" := (IsSubtype lhs rhs) (at level 63, no associativity).

Definition IsSupertype {A: Set} {IS: ISOf A} (lhs rhs: A): Prop := lhs I rhs :> rhs.
Notation "'(:>)'" := IsSupertype.
Notation "lhs ':>' rhs" := (IsSupertype lhs rhs) (at level 63, no associativity).

Definition IsBounded {A: Set} {US: USOf A} (x min max: A): Prop := min U x <: x /\ x U max <: max.
Notation "min '<:' x '<:' max" := (IsBounded x min max) (at level 64, no associativity).

Definition IsBoundedAlt {A: Set} {US: USOf A} {IS: ISOf A} (x min max: A): Prop := min I x :> min /\ x I max :> x.
Notation "max ':>' x ':>' min" := (IsBoundedAlt x min max) (at level 64, no associativity).

Definition Union {A: Set} {US: USOf A} (lhs rhs a: A): Prop := lhs U rhs <: a /\ forall b, lhs U rhs <: b -> a <: b.
Notation "'(U)'" := Union.
Notation "lhs 'U' rhs '=' a" := (Union lhs rhs a) (at level 60, rhs at next level, no associativity).

Definition Intersection {A: Set} {IS: ISOf A} (lhs rhs a: A): Prop := lhs I rhs :> a /\ forall b, lhs I rhs :> b -> a :> b.
Notation "'(I)'" := Intersection.
Notation "lhs 'I' rhs '=' a" := (Intersection lhs rhs a) (at level 60, rhs at next level, no associativity).

Theorem subtype_never: forall (a: ftype), FNEVER <: a.
Proof.
  intros. apply US_NeverL.
Qed.

Theorem subtype_null: forall (a: ftype), IsNullable a -> FNULL <: a.
Proof.
  intros. apply US_NullL. exact H.
Qed.

Theorem subtype_any: forall (a: ftype), a <: FAny.
Proof.
  intros. apply US_Any.
Qed.

Local Ltac ind1 a :=
  lazymatch type of a with
  | js_record _ => induction a using js_record_ind
  | list _ => induction a
  | _ => destruct a
  end.

Tactic Notation "induction2" ident (a) ident (b) "using" tactic (ind2) :=
  revert_with a; revert_with b; ind2 a b; intros.

Tactic Notation "induction3" ident (a) ident (b) ident (c) "using" tactic (ind3) :=
  revert_with a; revert_with b; revert_with c; ind3 a b c; intros.

Local Ltac ind2 a b :=
  lazymatch type of a with
  | js_record _ => induction2 a b using ind_js_record2
  | list _ => induction2 a b using ind_list2
  | _ => destruct a; destruct b
  end.

Local Ltac ind3 a b c :=
  lazymatch type of a with
  | js_record _ => induction3 a b c using ind_js_record3
  | list _ => induction3 a b c using ind_list3
  | _ => destruct a; destruct b; destruct c
  end.

Local Ltac ind_cs a b c :=
  lazymatch constr:((a, b, c)) with
  | (?a, ?a, ?a) => ind1 a
  | (?a, ?a, ?b) => ind2 a b
  | (?a, ?b, ?a) => ind2 a b
  | (?a, ?b, ?b) => ind2 a b
  | (?a, ?b, ?c) => ind3 a b c
  end.

Local Ltac inv_con2 a :=
  let Inv := fresh "Inv" in
  match goal with
  | Inv' : ?P ?a' |- _ => constr_eq a' a; rename Inv' into Inv
  | _ => idtac
  end;
  ind1 a; try (inv Inv); try constructor; invert_eqs; simpl; try (reflexivity || discriminate).

Local Ltac is_var' a := first [is_var a | is_evar a].

Local Ltac inv_con1 a :=
  tryif is_var' a then inv_con2 a else fail "tried to inv_con non-variables".

Local Ltac inv_con0 a :=
  lazymatch a with
  | ?P ?a => inv_con1 a
  | ?a => inv_con1 a
  end.

Local Ltac post_inv_con :=
  lazymatch goal with
  (* Solvers *)
  | G : ?P |- ?P => exact G
  | G : ?P /\ ?Q |- ?P => destruct G as [G _]; exact G
  | G : ?P /\ ?Q |- ?Q => destruct G as [_ G]; exact G
  (* Inductive hypothesis *)
  | IH : ?Q -> ?Q0 -> ?Q1 -> ?Q2 -> ?P |- ?P => apply IH; post_inv_con
  | IH : ?Q -> ?Q0 -> ?Q1 -> ?P |- ?P => apply IH; post_inv_con
  | IH : ?Q -> ?Q0 -> ?P |- ?P => apply IH; post_inv_con
  | IH : ?Q -> ?P |- ?P => apply IH; post_inv_con
  | |- ?a && ?a >= ?a => destruct a; reflexivity
  | |- ?a >= ?a || ?a => destruct a; reflexivity
  | G : forall (a: ftype), a I a :> a /\ a U a <: a |- ?a I ?a :> ?a => specialize (G a); destruct G as [G _]; exact G || fail "mismatched inductive end-case"
  | G : forall (a: ftype), a I a :> a /\ a U a <: a |- ?a U ?a <: ?a => specialize (G a); destruct G as [_ G]; exact G || fail "mismatched inductive end-case"
  | |- _ => idtac
  end.

(* Destruct or induct on goal, invert dependent hypotheses, apply the corresponding constructor *)
Local Ltac inv_con :=
  lazymatch goal with
  | |- [_] ?a I ?a :> ?a => inv_con0 a
  | |- [_] ?a U ?a <: ?a => inv_con0 a
  | |- _ => fail "not inv_con supported"
  end; post_inv_con.

Local Ltac inv_con' := repeat progress inv_con.

Theorem subtype_supertype_refl: forall (a: ftype), a :> a /\ a <: a.
Proof.
  induction a using ftype_rec'; intros; split; intros; unfold IsSubtype, IsSupertype in *.
  all: try (constructor; fail).
  all: try (destruct nullable; constructor; simpl; reflexivity).
  all: constructor; try (destruct nullable; simpl; reflexivity).
  all: try (inv_con0 structure).
  all: try (inv_con0 tparams).
  all: try (inv_con0 a).
  all: try (inv_con0 v).
  all: try (inv_con0 supers; econstructor; [destruct H1; exact c || exact c0 | ..]).
  all: try (apply IHsupers; assumption).
  all: try (apply List.Add_head; fail).
  all: try (inv_con0 tparams).
  all: try (inv_con0 a).
  all: try (inv_con0 v).

  econstructor.
  all: (inv_con0 structure).
  all: try (destruct structure; inv H; constructor).
  all: try (induction tparams; inv H5; constructor).
    (constructor; try (destruct nullable; simpl; reflexivity); inv_con').
    try (unshelve econstructor; [exact a | exact supers | | apply List.Add_head]; post_inv_con);
    try (destruct x as [kv vx]; unshelve econstructor; [exact vx | exact l | | apply JsRecordAdd_head]; simpl in H0; inv_con; simpl in H2; inv H2; destruct H5; assumption);
    try (unshelve econstructor; [exact id | exact sids | | apply List.Add_head ]; inv_con').
Qed.

Corollary subtype_refl: forall (a: ftype), a <: a.
Proof.
  intros. apply subtype_supertype_refl.
Qed.

Corollary supertype_refl: forall (a: ftype), a :> a.
Proof.
  intros. apply subtype_supertype_refl.
Qed.

Theorem subtype_supertype_antisym: forall (a b: ftype), (a <: b -> b :> a) /\ (a :> b -> b <: a).
Proof.
  split; intros; induction H.
  all: try (constructor; simpl; easy).
  all: try apply subtype_supertype_refl.
  all: try (destruct lhs; constructor; assumption).
  all: repeat constructor.
  all: try (destruct nu; destruct nl; simpl; easy).
  all: try (destruct ou; destruct ol; simpl; easy).
  ind3 tpl tpr tpu; [constructor | inv_cs H4 | inv_cs H4 | constructor | inv_cs H4 | inv_cs H4 | inv_cs H4 | inv_cs H4].

  ind3 tpl tpr tpu; [constructor | inv H4 | inv H4 | constructor | inv H4 | inv H4 | inv H4 | apply inv_IS_Zip_cons in H4; destruct H4; constructor]; [| apply H; exact H5].

(* Has extra cases for the specific theorem we're trying to prove *)
Local Ltac post_inv_con_hook ::=
  lazymatch goal with
  | G : forall (a: ftype), (?b U a <: a -> a I ?b :> ?b) /\ (?b I a :> a -> a U ?b <: ?b) |- ?a I ?b :> ?b => specialize (G a); destruct G as [G _]; apply G
  | G : forall (a: ftype), (?b U a <: a -> a I ?b :> ?b) /\ (?b I a :> a -> a U ?b <: ?b) |- ?a U ?b <: ?b => specialize (G a); destruct G as [_ G]; apply G
  | |- ?a I ?a :> ?a => apply subtype_supertype_refl
  | |- ?a U ?a <: ?a => apply subtype_supertype_refl
  | |- _ => idtac
  end.

Theorem subtype_supertype_antisym: forall (a b: ftype), (a <: b -> b :> a) /\ (a :> b -> b <: a).
Proof with inv_con'.
  first_inv_con a; try inv_con.
  1: inv H; constructor.
  1: inv H; destruct nullable; try constructor; simpl; reflexivity || assumption || discriminate.
  1: inv H; destruct nullable; try constructor; discr_relation_eqs; simpl; reflexivity || assumption || discriminate.
  - inv_con.
    + inv_con; inv H5.

  apply prove_relation_by_ftype2.
  - induction a using ftype_rec'; intros; split; intros; unfold IsSubtype, IsSupertype in *.
    inv_con. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con.
    inv_con. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con.
    inv_con. inv_con. inv_con. inv_con'0. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con'0.
    inv_con. inv_con. inv_con. inv_con. inv_con'0. inv_con. inv_con. inv_con'0. inv_con. inv_con'0.
    inv_con. inv_con. inv_con. inv_con. inv_con'0. inv_con. inv_con.
    inv_con. inv_con'0. inv_con'0. inv_con. inv_con. inv_con'0. inv_con. inv_con. inv_con. inv_con.

    + inv_con.
      destruct xs'; [constructor | inv H3; inv H7].
      destruct ys'; [constructor | inv H3; inv H8].
      destruct H2 as [k [[vx H2] [vy H5]]]. econstructor; [exact H2 | exact H5 | exact H5 | |];
        apply (JsRecordAdd_Forall H5) in H3; destruct H3. inv_con.
    + ind_cs fields fields0 fields0; [constructor | | |]; inv H2; [inv H6 | inv H7 | apply (JsRecordAdd_Forall H6) in H1; destruct H1; econstructor]; [exact H7 | exact H6 | exact H6 | |].
      inv_con. inv_con. inv_con'0.
    destruct xs'; [constructor | inv H3; inv H7].
    destruct ys'; [constructor | inv H3; inv H8].
    destruct xs'; destruct ys'; inv H4.
    econstructor.

    inv H3].

    inv H1. constructor.
    inv_con.
    replace (x :: xs)%list with (nil ++ (x :: xs))%list.
    apply US_NilOTypeL.
    inv_con. specialize (H6 thisp).
  try constructor; clear_relation_neqs; invert_eqs; simpl; try (reflexivity || discriminate).
    Print CommonSupertype.
    inv_con. inv_con. inv_con. inv_con. inv_con.
    inv_con.

    inv_con. inv_con. inv_con. inv_con. inv_con. inv_con. inv_con.
    inv_con. inv_con.

Theorem subtype_supertype_refl: forall {A: Set} {h: HasRelation A} (a: A), a :> a /\ a <: a.
Proof.
  apply prove_relation_by_ftype1.
  - induction a using ftype_rec'; intros; split; unfold IsSubtype, IsSupertype in *; repeat inv_con.
  - intros; split; unfold IsSubtype, IsSupertype in *; destruct_relation_type A h; repeat inv_con'.
Qed.

Admitted.

Theorem subtype_supertype_trans: forall {A: Set} {h: HasRelation A} (a b c: A),
    (a <: b -> b <: c -> a <: c) /\ (a :> b -> b :> c -> a :> c).
Admitted.


Local Ltac contstructor0 :=
  constructor || match goal with
  | |- context[(?x :: ?xs)%list] => destruct x; econstructor; [apply List.Add_head | |]
  | |- _ => fail "no constructor"
  end.

Local Ltac induction1 a b :=
  (revert_with a; revert_with b; ind_js_record2 a b; intros) ||
  (revert_with a; revert_with b; ind_list2 a b; intros) ||
  (destruct a).

Local Ltac induction0 a b :=
  lazymatch a with
  | Supers_ ?a => destruct a
  | ?a => induction1 a b
  end.

Local Ltac destruct_nullable :=
  lazymatch goal with
  | |- FNever ?nullable U FNever ?nullable <: _ => destruct nullable
  | |- FNever ?nullable I FNever ?nullable :> _ => destruct nullable
  end.

Local Ltac inv_con0 Inv H a b :=
  induction0 a b; try inv Inv; inv_cs H; try destruct_nullable;
  (reflexivity || assumption || discriminate || contradiction || econstructor || idtac "constructor failed").

Local Ltac inv_con :=
  lazymatch goal with
  | |- ?a U ?a <: ?a => apply subtype_refl
  | Ind : forall a : ftype, (a <: ?b -> a U a <: ?b) /\ (a :> ?b -> a I a :> ?b) |- ?a U ?a <: ?b =>
      specialize (Ind a); destruct Ind as [Ind _]; apply Ind; try assumption
  | Ind : forall a : ftype, (a <: ?b -> a U a <: ?b) /\ (a :> ?b -> a I a :> ?b) |- ?a I ?a :> ?b =>
      specialize (Ind a); destruct Ind as [_ Ind]; apply Ind; try assumption
  | IH : ?Q -> ?Q0 -> ?Q1 -> ?Q2 -> ?P |- ?P => apply IH
  | IH : ?Q -> ?Q0 -> ?Q1 -> ?P |- ?P => apply IH
  | IH : ?Q -> ?Q0 -> ?P |- ?P => apply IH
  | IH : ?Q -> ?P |- ?P => apply IH
  | Inv : ?P ?b, H : ?a U ?b <: ?b |- ?a U ?a <: ?b => inv_con0 Inv H a b
  | Inv : ?P ?b, H : ?a I ?b :> ?b |- ?a I ?a :> ?b => inv_con0 Inv H a b
  | H : ?a U ?b <: ?b |- ?a U ?a <: ?b => inv_con0 True H a b
  | H : ?a I ?b :> ?b |- ?a I ?a :> ?b => inv_con0 True H a b
  | H : ?a <: ?b |- ?a U ?a <: ?b => inv_con0 True H a b
  | H : ?a :> ?b |- ?a I ?a :> ?b => inv_con0 True H a b
  | Inv : ?P ?b |- ?a U ?a <: ?b => destruct a; inverts Inv; constructor
  | Inv : ?P ?b |- ?a I ?a :> ?b => destruct a; inverts Inv; constructor
  | |- (?t >= ?t2 || ?t2)%bool => destruct t; destruct t2
  | |- (?t <= ?t2 && ?t2)%bool => destruct t; destruct t2
  | |- ?a U ?b <: ?b => constructor
  | |- ?a U ?a <: ?b => fail "todo handle"
  | |- ?a I ?a :> ?b => fail "todo handle"
(*
  | H : ?P |- ?P => exact H
  | H : ?t U ?t = ?t /\ ?t I ?t = ?t |- ?t U ?t <: ?t => destruct H as [[H _] _]; exact H
  | H : ?t U ?t = ?t /\ ?t I ?t = ?t |- ?t I ?t :> ?t => destruct H as [_ [H _]]; exact H
  | |- (?t && ?t >= ?t)%bool => destruct t; simpl; reflexivity
  | |- (?t || ?t <= ?t)%bool => destruct t; simpl; reflexivity
  | IH : ?Q -> ?P |- ?P => apply IH
  | H : ?P (snd (_, ?t)) |- _ => simpl in H
  | H : ?P ?t |- ?t U ?t <: ?t => inv_con0 US_OTypes H t
  | H : ?P ?t |- ?t I ?t :> ?t => inv_con0 IS_OTypes H t
  | |- ?t U ?t <: ?t => induction' t; constructor
  | |- ?t I ?t :> ?t => induction' t; constructor
  | |- ?v U ?v <: ?v => fail "todo handle"
  | |- ?v I ?v :> ?v => fail "todo handle" *)
  end; cleanup.


Theorem subtype_alt: forall {A: Set} {h: HasRelation A} (a b: A),
    (a <: b -> a U a <: b) /\ (a :> b -> a I a :> b).
Proof.
  intros; destruct_relation_type A h.
  - revert a. induction b using ftype_rec'; split; intros;
      inv_cs H; try constructor;
        try (destruct nullable; simpl in *; try constructor; (reflexivity || contradiction || discriminate || assumption)).
      repeat inv_con.
      repeat inv_con.
      repeat inv_con.
      inv_con. inv_con. inv_con.
      + inv_cs H3; try constructor.
        destruct (JsRecordAdd_forall H6 H1), (JsRecordAdd_forall H6 H1). simpl in H, H2. inverts H. inverts H2. rename x into vr.
        econstructor; [exact H5 | | exact H7 | | ].
        2: {
          exact
        }
        inv_con. inv_con. inv_con.
        inv_con. inv_con. inv_con.
      + econstructor.
      + inverts H1; [econstructor; [apply List.Add_head | repeat inv_con | repeat inv_con] |].
        inverts H7.
        induction H8. inv_cs H7. cleanup.
        econstructor. apply List.Add_cons. Print List.

      +
      + revert_with params'; ind_list2_alt params0' params'; intros.
        * exact H9.
        * inv_cs H9; cleanup.

      try destruct nullable; try constructor.
      try destruct nullable; try destruct nl; simpl in *; invert_eqs; clear_obvious; try (constructor || discriminate).
        try constructor; simpl in *; try (constructor || discriminate); clear_obvious; invert_eqs;
      idtac. Focus 8.
    + destruct nullable; try discriminate.
    + inv_cs H; constructor.

    inv_cs H

Theorem supertype_never: forall (a: ftype), a :> FNEVER.
Proof.
  intros. apply IS_Never.
Qed.

Theorem supertype_null: forall (a: ftype), IsNullable a -> a :> FNULL.
Proof.
  intros. apply IS_Null. exact H. by_ simpl.
Qed.

Theorem supertype_any: forall (a: ftype), FAny :> a.
Proof.
  intros. apply IS_AnyL.
Qed.

Theorem supertype_refl: forall {A: Set} {h: HasRelation A} (a: A), a :> a.
Admitted.

Theorem supertype_antisym: forall {A: Set} {h: HasRelation A} (a b: A), a :> b -> b <: a.
Admitted.

Theorem supertype_trans: forall {A: Set} {h: HasRelation A} (a b c: A), a :> b -> b :> c -> a :> c.
Admitted.

Theorem union_never: forall (a: ftype), FNEVER U a = a.
Proof.
  intros. split.
  - apply US_NeverL.
  - intros. revert H. destruct a; destruct b; simpl; intros;
      try apply US_Any;
      try solve [inv_cs H].
    + inv_cs H; try inverts H0; try inverts H1; try inverts H2; by_ auto.
    + inv_cs H. inverts H0. by_ auto.
    + inv_cs H. inverts H0. by_ auto.
Qed.

Theorem union_null: forall (a: ftype), IsNullable a -> FNULL U a = a.
Proof.
  intros. split.
  - apply US_NullL. exact H.
  - intros. rename H into H1, H0 into H. revert H. destruct a; destruct b; simpl; intros;
      try apply US_Any;
      try discr_cs H.
    + inv_cs H; try inverts H0; try inverts H1; try inverts H2; by_ auto.
    + inv_cs H. inverts H0. by_ auto.
    + inv_cs H. inverts H0. by_ auto.
Qed.

Theorem union_any: forall (a: ftype), FAny U a = FAny.
Proof.
  intros. split.
  - apply US_Any.
  - intros. revert H. destruct a; destruct b; simpl; intros;
      try apply US_Any;
      try discr_cs H.
Qed.

Print ftype_ind.

Local Ltac induction' H :=
  lazymatch H with
  | Rev_ ?t => induction t
  | Supers_ ?t => destruct t
  | ?t => induction t
  end.

Local Ltac contstructor0 :=
  constructor + match goal with
  | |- context[(?x :: ?xs)%list] => destruct x; econstructor; [apply List.Add_head | |]
  | |- _ => fail "no constructor"
  end.

Local Ltac inv_ap0 Constr H t :=
  tryif apply Constr then (
    apply List.Forall_rev in H; remember (List.rev _) as t2 eqn:H0; clear H0;
      induction t2; inverts H; constructor
  ) else (
    induction' t; inverts H; contstructor0; try discriminate
  ).

Local Ltac inv_ap :=
  lazymatch goal with
  | H : ?P |- ?P => exact H
  | H : ?t U ?t = ?t /\ ?t I ?t = ?t |- ?t U ?t <: ?t => destruct H as [[H _] _]; exact H
  | H : ?t U ?t = ?t /\ ?t I ?t = ?t |- ?t I ?t :> ?t => destruct H as [_ [H _]]; exact H
  | |- (?t && ?t >= ?t)%bool => destruct t; simpl; reflexivity
  | |- (?t || ?t <= ?t)%bool => destruct t; simpl; reflexivity
  | IH : ?Q -> ?P |- ?P => apply IH
  | H : ?P (snd (_, ?t)) |- _ => simpl in H
  | H : ?P ?t |- ?t U ?t <: ?t => inv_ap0 US_OTypes H t
  | H : ?P ?t |- ?t I ?t :> ?t => inv_ap0 IS_OTypes H t
  | |- ?t U ?t <: ?t => induction' t; constructor
  | |- ?t I ?t :> ?t => induction' t; constructor
  | |- ?v U ?v <: ?v => fail "todo handle"
  | |- ?v I ?v :> ?v => fail "todo handle"
  end.

Local Ltac destruct_nullable H :=
  repeat lazymatch goal with | H : bool |- _ => destruct H end;
  simpl; try (reflexivity + inv_cs H; invert_eqs; simpl in *; discriminate).

Local Ltac inv_cs' H :=
  inv_cs H; invert_eqs; simpl in *; clear_obvious.

Local Ltac revert_with t :=
  repeat lazymatch goal with
  | H : context[t] |- _ => revert H
  end.

Local Ltac destruct2' a b :=
  (revert_with a; revert_with b; ind_list2 a b; intros) +
    (destruct a; destruct b).

Local Ltac destruct2 a b :=
  lazymatch a with
  | Supers_ ?a => match b with Supers_ ?b => destruct2' a b end
  | Rev_ ?a => lazymatch b with Rev_ ?b => destruct2' a b end
  | _ => destruct2' a b
  end.

Local Ltac ap_inv0_oftype H H0 params params0 :=
  inv_cs' H0; constructor; apply List.Forall_rev in H;
    remember (List.rev params) as params' eqn:Heqparams'; remember (List.rev params0) as params0' eqn:Heqparams0';
    clear Heqparams'; clear Heqparams0'; clear params; clear params0.

Local Ltac ap_inv0 H H0 t t2 :=
  match type of t with
  | list oftype => ap_inv0_oftype H H0 t t2
  | _ => destruct2 t t2; inverts H; inv_cs' H0; try constructor
  end.

Local Ltac ap_inv :=
  lazymatch goal with
  | H : ?t U ?t = ?t /\ ?t I ?t = ?t |- ?t U ?t <: ?t => destruct H as [[H _] _]; exact H
  | H : ?t U ?t = ?t /\ ?t I ?t = ?t |- ?t I ?t :> ?t => destruct H as [_ [H _]]; exact H
  | H : ?t U ?t = ?t /\ ?t I ?t = ?t |- ?t U ?t2 <: ?t2 => destruct H as [[_ H] _]; apply H; assumption
  | H : ?t U ?t = ?t /\ ?t I ?t = ?t |- ?t I ?t2 :> ?t2 => destruct H as [_ [_ H]]; apply H; assumption
  | IH : ?Q -> ?Q0 -> ?Q1 -> ?P |- ?P => apply IH; try assumption
  | IH : ?Q -> ?Q0 -> ?P |- ?P => apply IH; try assumption
  | IH : ?Q -> ?P |- ?P => apply IH; try assumption
  | H : ?P ?t |- ?t U ?t <: ?t => inverts H; constructor
  | H : ?P ?t |- ?t I ?t :> ?t => inverts H; constructor
  | H : ?P ?t, H0 : Rev_ ?t U Rev_ ?t <: Rev_ ?t2 |- Rev_ ?t U Rev_ ?t2 <: Rev_ ?t2 => ap_inv0 H H0 t t2
  | H : ?P ?t, H0 : Rev_ ?t I Rev_ ?t :> Rev_ ?t2 |- Rev_ ?t I Rev_ ?t2 :> Rev_ ?t2 => ap_inv0 H H0 t t2
  | H : ?P ?t, H0 : ?t U ?t <: ?t2 |- ?t U ?t2 <: ?t2 => ap_inv0 H H0 t t2
  | H : ?P ?t, H0 : ?t I ?t :> ?t2 |- ?t I ?t2 :> ?t2 => ap_inv0 H H0 t t2
  | H0 : ?t U ?t <: ?t2 |- ?t U ?t2 <: ?t2 => destruct2 t t2; inv_cs' H0; constructor
  | H0 : ?t I ?t :> ?t2 |- ?t I ?t2 :> ?t2 => destruct2 t t2; inv_cs' H0; constructor
  | |- ?t U ?t2 <: ?t2 => destruct2 t t2; constructor
  | |- ?t I ?t2 :> ?t2 => destruct2 t t2; constructor
  | |- (?t && ?t >= ?t)%bool => destruct t; simpl; reflexivity
  | |- (?t || ?t <= ?t)%bool => destruct t; simpl; reflexivity
  | |- (?t && ?t2 >= ?t2)%bool => destruct2 t t2; simpl in *; try (reflexivity + discriminate); clear_obvious
  | |- (?t || ?t2 <= ?t2)%bool => destruct2 t t2; simpl in *; try (reflexivity + discriminate); clear_obvious
  end.


Theorem union_intersect_refl : forall {A: Set} {h: HasRelation A} (a: A), a U a = a /\ a I a = a.
Proof.
  intros; destruct_relation_type A h.
  - induction a using ftype_rec'.
    * split; split; intros; try constructor; inv_cs H; constructor.
    * split; split; destruct nullable; intros;
        try inv_cs H;
        constructor;
        try (simpl; reflexivity);
        try exact H3.
    * split; split; intros; try constructor;
        try (destruct nullable; simpl; reflexivity).
      + repeat inv_ap.
      + destruct b; try constructor; destruct_nullable H0; inv_cs' H0.
        ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv.
        revert_with params'; ind_list2_alt params' params0'; intros; inverts H8;
          [apply IS_NilOType |  | |].
          [apply IS_NilOType | inv_cs' H5 | apply IS_ConsOTypeR; apply H; [apply List.Forall_nil | inv_cs' H5; assumption] | inv_cs' H5].
          apply IS_ConsOType; [ap_inv; ap_inv | apply H; assumption].
          apply IS_ConsOTypeL.
        inverts H4; inv_cs' H5.
        destruct optional; destruct optional0;
          try (apply IS_ConsOType; [constructor; [simpl; reflexivity | ap_inv] | ]).
          try (apply IS_ConsOType; [inverts H4; constructor; [reflexivity | ] |]).
          inverts H8; inv_cs' H5.
        ap_inv.
        ap_inv. ap_inv. ap_inv.
        ap_inv.
        ap_inv. ap_inv. ap_inv.
        apply H; try assumption. inv_cs' H14.


        [constructor | constructor | |]. constructor.

          inverts H8; [simpl in *; subst |].
        destruct2 params params0; inverts H8; inv_cs' H4. try constructor.
        constructor. simpl

        revert_with tparams; ind_list2 tparams tparams0; intros;
          inverts H6; inv_cs' H2; try constructor.
        revert_with tparams; ind_list2 tparams tparams0; intros;
          try constructor; inv_cs' H5; inv_cs' H3; inverts H6.
        destruct x; destruct y; inverts H2; inv_cs' H5; try constructor.
        destruct v; destruct v0; inv_cs' H15; try constructor.
        revert_with supers; ind_list2 supers supers0; intros;
          try constructor; inv_cs' H16.
        rename H into IH; apply IH; try constructor; assumption.
        destruct H7 as [_ [_ H7]]; apply H7; inv_cs' H5; assumption.



        inverts H. destruct
        ap_inv. inv_cs' H5.  ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv.
        ap_inv. revert_with tparams0. ind_list2 tparams0 tparams1.
        ap_inv.

        ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv.
        ap_inv.
        ap_inv.
        induction' structure; destruct structure0.



        ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv. ap_inv.
        ap_inv. ap_inv. ap_inv.
        induction b; try constructor;
          destruct_nullable H0.
        ap_inv. ap_inv.
        induction' b; try constructor;
          destruct_nullable H0.
          inverts H.
        induction' structure0; try constructor. etc.

Theorem union_insersect_sym : forall {A: Set} {h: HasRelation A} (a b c: A),
    (a U b = c -> b U a = c) /\ (a I b = c -> b I a = c).
Admitted.

Theorem union_intersecttrans : forall {A: Set} {h: HasRelation A} (a b c x y z: A),
    (a U b = x -> b U c = y -> (a U c = z <-> x U y = z)) /\ (a I b = x -> b I c = y -> (a I c = z <-> x I y = z)).
Admitted.
