(* -*- company-coq-local-symbols: (("U" . ?∪) ("I" . ?∩)); -*- *)
(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Add LoadPath "tlc/src" as TLC.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
From NS Require Import Misc.
From NS Require Import TypesBase.
From NS Require Import TypesNotation.
From NS Require Import TypesSimpleHelpers.

Inductive Rev := Rev_ (a: list (otype ftype)).
Inductive Supers := Supers_ (a: list ftype).

Local Notation list_ftype := (list ftype) (only parsing).
Local Notation list_iftype := (list iftype) (only parsing).
Local Notation list_oftype := (list oftype) (only parsing).
Local Notation list_ftparam := (list ftparam) (only parsing).
Local Notation js_record_ftype := (js_record ftype) (only parsing).
Local Notation js_record_oftype := (js_record oftype) (only parsing).
Local Notation option_sftype := (option sftype) (only parsing).

Inductive RelationType : Set :=
| ftype_RelationType
| iftype_RelationType
| sftype_RelationType
| oftype_RelationType
| vftype_RelationType
| ftparam_RelationType
| variance_RelationType
| list_ftype_RelationType
| list_iftype_RelationType
| list_oftype_RelationType
| list_ftparam_RelationType
| js_record_ftype_RelationType
| js_record_oftype_RelationType
| option_sftype_RelationType
| Rev_RelationType
| Supers_RelationType.
Class HasRelation (A: Set) := { relation_type : RelationType }.
Global Instance ftype_HasRelation : HasRelation ftype := { relation_type := ftype_RelationType }.
Global Instance iftype_HasRelation : HasRelation iftype := { relation_type := iftype_RelationType }.
Global Instance sftype_HasRelation : HasRelation sftype := { relation_type := sftype_RelationType }.
Global Instance oftype_HasRelation : HasRelation oftype := { relation_type := oftype_RelationType }.
Global Instance vftype_HasRelation : HasRelation vftype := { relation_type := vftype_RelationType }.
Global Instance ftparam_HasRelation : HasRelation ftparam := { relation_type := ftparam_RelationType }.
Global Instance variance_HasRelation : HasRelation variance := { relation_type := variance_RelationType }.
Global Instance list_ftype_HasRelation : HasRelation list_ftype := { relation_type := list_ftype_RelationType }.
Global Instance list_iftype_HasRelation : HasRelation list_iftype := { relation_type := list_iftype_RelationType }.
Global Instance list_oftype_HasRelation : HasRelation list_oftype := { relation_type := list_oftype_RelationType }.
Global Instance list_ftparam_HasRelation : HasRelation list_ftparam := { relation_type := list_ftparam_RelationType }.
Global Instance js_record_ftype_HasRelation : HasRelation js_record_ftype := { relation_type := js_record_ftype_RelationType }.
Global Instance js_record_oftype_HasRelation : HasRelation js_record_oftype := { relation_type := js_record_oftype_RelationType }.
Global Instance option_sftype_HasRelation : HasRelation option_sftype := { relation_type := option_sftype_RelationType }.
Global Instance Rev_HasRelation : HasRelation Rev := { relation_type := Rev_RelationType }.
Global Instance Supers_HasRelation : HasRelation Supers := { relation_type := Supers_RelationType }.
Axiom relation_type_eq : forall {A B: Set} {h1: HasRelation A} {h2: HasRelation B},
    (@relation_type A h1 = @relation_type B h2 -> A = B /\ h1 ~= h2) /\
    (A = B \/ h1 ~= h2 -> @relation_type A h1 = @relation_type B h2).
Lemma relation_type_eq0 : forall {A: Set} {h: HasRelation A},
  (ftype_RelationType = @relation_type A h -> A = ftype /\ h ~= ftype_HasRelation) /\
  (iftype_RelationType = @relation_type A h -> A = iftype /\ h ~= iftype_HasRelation) /\
  (sftype_RelationType = @relation_type A h -> A = sftype /\ h ~= sftype_HasRelation) /\
  (oftype_RelationType = @relation_type A h -> A = oftype /\ h ~= oftype_HasRelation) /\
  (vftype_RelationType = @relation_type A h -> A = vftype /\ h ~= vftype_HasRelation) /\
  (ftparam_RelationType = @relation_type A h -> A = ftparam /\ h ~= ftparam_HasRelation) /\
  (variance_RelationType = @relation_type A h -> A = variance /\ h ~= variance_HasRelation) /\
  (list_ftype_RelationType = @relation_type A h -> A = list_ftype /\ h ~= list_ftype_HasRelation) /\
  (list_iftype_RelationType = @relation_type A h -> A = list_iftype /\ h ~= list_iftype_HasRelation) /\
  (list_oftype_RelationType = @relation_type A h -> A = list_oftype /\ h ~= list_oftype_HasRelation) /\
  (list_ftparam_RelationType = @relation_type A h -> A = list_ftparam /\ h ~= list_ftparam_HasRelation) /\
  (js_record_ftype_RelationType = @relation_type A h -> A = js_record_ftype /\ h ~= js_record_ftype_HasRelation) /\
  (js_record_oftype_RelationType = @relation_type A h -> A = js_record_oftype /\ h ~= js_record_oftype_HasRelation) /\
  (option_sftype_RelationType = @relation_type A h -> A = option_sftype /\ h ~= option_sftype_HasRelation) /\
  (Rev_RelationType = @relation_type A h -> A = Rev /\ h ~= Rev_HasRelation) /\
  (Supers_RelationType = @relation_type A h -> A = Supers /\ h ~= Supers_HasRelation).
Proof.
  repeat split; intros; apply relation_type_eq; simpl; symmetry; exact H.
Qed.
Lemma relation_type_eq1 : forall {A B: Set} {h1: HasRelation A} {h2: HasRelation B},
    A = B -> @relation_type A h1 = @relation_type B h2.
Proof.
  intros. apply relation_type_eq. left. exact H.
Qed.
Ltac destruct_relation_type A h :=
  remember (@relation_type A h) as hRel eqn:hEq; destruct hRel; apply relation_type_eq0 in hEq; destruct hEq; subst.

Local Notation "a <= b" := (Bool.le a b) : bool_scope.
Local Notation "a >= b" := (Bool.le b a) : bool_scope.
Reserved Notation "a 'U' b '<:' c" (at level 60, b at next level, no associativity).
Reserved Notation "a 'I' b ':>' c" (at level 60, b at next level, no associativity).
Inductive CommonSupertype : forall {A: Set} {h: HasRelation A}, A -> A -> A -> Prop :=
| US_Any             : forall (lhs rhs: ftype), lhs U rhs <: FAny
| US_NeverL          : forall (rhs: ftype), FNEVER U rhs <: rhs
| US_NeverR          : forall (lhs: ftype), lhs U FNEVER <: lhs
| US_NullL           : forall (rhs: ftype), IsNullable rhs -> FNULL U rhs <: rhs
| US_NullR           : forall (lhs: ftype), IsNullable lhs -> lhs U FNULL <: lhs
| US_Struct          : forall (nl nr nu: bool) (sl sr su: stype ftype),
    nl || nr <= nu -> sl U sr <: su -> FStructural nl sl U FStructural nr sr <: FStructural nu su
| US_NomStruct       : forall (nl nr nu: bool) (idl: itype ftype) (idsl: list (itype ftype)) (sl sr su: stype ftype),
    nl || nr <= nu -> sl U sr <: su -> FNominal nl idl idsl (Some sl) U FStructural nr sr <: FStructural nu su
| US_StructNom       : forall (nl nr nu: bool) (idr: itype ftype) (idsr: list (itype ftype)) (sl sr su: stype ftype),
    nl || nr <= nu -> sl U sr <: su -> FStructural nl sl U FNominal nr idr idsr (Some sr) <: FStructural nu su
| US_NomCommonNom    : forall (nl nr nu: bool) (idl idr idu: itype ftype) (idsl idsr idsu: list (itype ftype)) (sl sr su: option (stype ftype)),
    nl || nr <= nu -> cons idl idsl U cons idr idsr <: cons idu idsu -> sl U sr <: su ->
    FNominal nl idl idsl sl U FNominal nr idr idsr sr <: FNominal nu idu idsu su
| US_NomCommonStruct : forall (nl nr nu: bool) (idl idr: itype ftype) (idsl idsr: list (itype ftype)) (sl sr su: stype ftype),
    nl || nr <= nu -> sl U sr <: su -> FNominal nl idl idsl (Some sl) U FNominal nr idr idsr (Some sr) <: FStructural nu su
(* with CommonSupertype_ident : itype ftype -> itype ftype -> itype ftype -> Prop := *)
| US_Ident           : forall (name: string) (tal tar tau: list ftype), tal U tar <: tau -> It name tal U It name tar <: It name tau
(* with CommonSupertype_struct : stype ftype -> stype ftype -> stype ftype -> Prop := *)
| US_Fn              : forall (tpl tpr tpu: list (tparam ftype)) (thispl thispr thispu: ftype)
                             (pl pr pu: list (otype ftype)) (rl rr ru: ftype) (retl retr retu: vtype ftype),
    tpl I tpr :> tpu -> thispl I thispr :> thispu -> pl I pr :> pu -> rl I rr :> ru -> retl U retr <: retu ->
    SFn tpl thispl pl rl retl U SFn tpr thispr pr rr retr <: SFn tpu thispu pu ru retu
| US_Array           : forall (el er eu: ftype),                      el U er <: eu    -> SArray el   U SArray er   <: SArray eu
| US_Tuple           : forall (esl esr esu: list (otype ftype)),      esl U esr <: esu -> STuple esl  U STuple esr  <: STuple esu
| US_Object          : forall (fsl fsr fsu: js_record (otype ftype)), fsl U fsr <: fsu -> SObject fsl U SObject fsr <: SObject fsu
(* with CommonSupertype_otype : otype ftype -> otype ftype -> otype ftype -> Prop := *)
| US_OType           : forall (ol or ou: bool) (lhs rhs uni: ftype), ol || or <= ou -> lhs U rhs <: uni -> Ot ol lhs U Ot or rhs <: Ot ou uni
(* with CommonSupertype_void : vtype ftype -> vtype ftype -> vtype ftype -> Prop := *)
| US_Void            : @VVoid ftype U VVoid <: VVoid
| US_NotVoid         : forall (lhs rhs uni: ftype), lhs U rhs <: uni -> Vt lhs U Vt rhs <: Vt uni
(* with CommonSupertype_tparam : tparam -> tparam -> tparam -> Prop := *)
| US_TParam          : forall (vl vr vu: variance) (name: string) (supl supr supu: list ftype),
    vl U vr <: vu -> Supers_ supl U Supers_ supr <: Supers_ supu ->
    TParam vl name supl U TParam vr name supr <: TParam vu name supu
(* with CommonSupertype_zip_ftype : list ftype -> list ftype -> list ftype -> Prop := *)
| US_NilFType        : @nil ftype U nil <: nil
| US_ConsFType       : forall (xl xr xu: ftype) (xsl xsr xsu: list ftype),
    xl U xr <: xu -> xsl U xsr <: xsu -> cons xl xsl U cons xr xsr <: cons xu xsu
(* with CommonSupertype_zip_tparam : list tparam -> list tparam -> list tparam -> Prop := *)
| US_NilTParam       : @nil (tparam ftype) U nil <: nil
| US_ConsTParam     : forall (xl xr xu: tparam ftype) (xsl xsr xsu: list (tparam ftype)),
    xl U xr <: xu -> xsl U xsr <: xsu -> cons xl xsl U cons xr xsr <: cons xu xsu
(* with CommonSupertype_zip_otype : list (otype ftype) -> list (otype ftype) -> list (otype ftype) -> Prop := *)
| US_OTypes          : forall (xsl xsr xsu: list (otype ftype)),
    Rev_ (List.rev xsl) U Rev_ (List.rev xsr) <: Rev_ (List.rev xsu) -> xsl U xsr <: xsu
(* with CommonSupertype_intersect_itype : list (itype ftype) -> list (itype ftype) -> list (itype ftype) -> Prop := *)
| US_IntersectNil    : forall (idsl idsr: list (itype ftype)), idsl U idsr <: nil
| US_IntersectConsL  : forall (idl: itype ftype) (idsl idsr idsu: list (itype ftype)), cons idl idsl U idsr <: idsu
| US_IntersectConsR  : forall (idr: itype ftype) (idsl idsr idsu: list (itype ftype)), idsl U cons idr idsr <: idsu
| US_IntersectInR    : forall (idl idr idu: itype ftype) (idsl idsr idsr' idsu: list (itype ftype)),
     List.Add idr idsr idsr' -> idl U idr <: idu -> idsl U idsr <: idsu -> cons idl idsl U idsr' <: cons idu idsu
| US_IntersectInL    : forall (idl idr idu: itype ftype) (idsl idsr idsl' idsu: list (itype ftype)),
     List.Add idl idsl idsl' -> idl U idr <: idu -> idsl U idsr <: idsu -> idsl' U cons idr idsr <: cons idu idsu
(* with CommonSupertype_zip_otype_rev : Rev (list (otype ftype)) -> Rev (list (otype ftype)) -> Rev (list (otype ftype)) -> Prop := *)
| US_NilOType        : Rev_ (@nil (otype ftype)) U Rev_ nil <: Rev_ nil
| US_ConsOType       : forall (xl xr xu: otype ftype) (xsl xsr xsu: list (otype ftype)),
    xl U xr <: xu -> Rev_ xsl U Rev_ xsr <: Rev_ xsu -> Rev_ (cons xl xsl) U Rev_ (cons xr xsr) <: Rev_ (cons xu xsu)
| US_ConsOTypeL      : forall (xsl xsr xsu: list (otype ftype)) (xl: otype ftype),
    Rev_ xsl U Rev_ xsr <: Rev_ xsu -> Rev_ (cons xl xsl) U Rev_ xsr <: Rev_ xsu
| US_ConsOTypeR      : forall (xsl xsr xsu: list (otype ftype)) (xr: otype ftype),
    Rev_ xsl U Rev_ xsr <: Rev_ xsu -> Rev_ xsl U Rev_ (cons xr xsr) <: Rev_ xsu
(* with CommonSupertype_intersect_ftype_supers : Supers (list ftype) -> Supers (list ftype) -> Supers (list ftype) -> Prop := *)
| US_IntSupersNil    : Supers_ (@nil ftype) U Supers_ nil <: Supers_ nil
| US_IntSupersConsL  : forall (xl: ftype) (xsl xsr xsu: list ftype), Supers_ (cons xl xsl) U Supers_ xsr <: Supers_ xsu
| US_IntSupersConsR  : forall (xr: ftype) (xsl xsr xsu: list ftype), Supers_ xsl U Supers_ (cons xr xsr) <: Supers_ xsu
| US_IntSupersInR    : forall (xl xr xu: ftype) (xsl xsr xsr' xsu: list ftype),
     List.Add xr xsr xsr' -> xl U xr <: xu -> xsl U xsr <: xsu -> Supers_ (cons xl xsl) U Supers_ xsr' <: Supers_ (cons xu xsu)
| US_IntSupersInL    : forall (xl xr xu: ftype) (xsl xsr xsl' xsu: list ftype),
     List.Add xl xsl xsl' -> xl U xr <: xu -> xsl U xsr <: xsu -> Supers_ xsl' U Supers_ (cons xr xsr) <: Supers_ (cons xu xsu)
(* with CommonSupertype_js_record : js_record oftype -> js_record oftype -> js_record oftype -> Prop *)
| US_JSNil           : @nil (string * oftype) U nil <: nil
| US_JSInR           : forall (name: string) (vl vr vu: oftype) (vls vrs vrs' vus: js_record oftype),
    List.Add (name, vr) vrs vrs' -> vl U vr <: vu -> vls U vrs <: vus -> cons (name, vl) vls U vrs' <: cons (name, vu) vus
| US_JSInL           : forall (name: string) (vl vr vu: oftype) (vls vls' vrs vus: js_record oftype),
    List.Add (name, vl) vls vls' -> vl U vr <: vu -> vls U vrs <: vus -> vls' U cons (name, vr) vrs <: cons (name, vu) vus
(* with CommonSupertype_variance : variance -> variance -> variance -> Prop *)
| US_Bivariant       : forall (lhs rhs: variance), lhs U rhs <: Bivariant
| US_Covariant       : Covariant U Covariant <: Covariant
| US_Contravariant   : Contravariant U Contravariant <: Contravariant
| US_InvariantL      : forall (rhs: variance), Invariant U rhs <: rhs
| US_InvariantR      : forall (lhs: variance), lhs U Invariant <: lhs
where "a 'U' b '<:' c" := (CommonSupertype a b c)
with CommonSubtype : forall {A: Set}, A -> A -> A -> Prop :=
| IS_Never           : forall (lhs rhs: ftype), lhs I rhs :> FNEVER
| IS_Null            : forall (lhs rhs: ftype), IsNullable lhs -> IsNullable rhs -> lhs I rhs :> FNULL
| IS_AnyL            : forall (rhs: ftype), FAny I rhs :> rhs
| IS_AnyR            : forall (lhs: ftype), lhs I FAny :> lhs
| IS_Struct          : forall (nl nr nu: bool) (sl sr su: stype ftype),
    nl && nr >= nu -> sl I sr :> su -> FStructural nl sl I FStructural nr sr :> FStructural nu su
| IS_NomStruct       : forall (nl nr nu: bool) (idl idu: itype ftype) (idsl idsu: list (itype ftype)) (sl sr su: stype ftype),
    nl && nr >= nu -> cons idl idsl I nil :> cons idu idsu -> sl I sr :> su ->
    FNominal nl idl idsl (Some sl) I FStructural nr sr :> FNominal nu idu idsu (Some su)
| IS_StructNom       : forall (nl nr nu: bool) (idr idu: itype ftype) (idsr idsu: list (itype ftype)) (sl sr su: stype ftype),
    nl && nr >= nu -> nil I cons idr idsr :> cons idu idsu -> sl I sr :> su ->
    FStructural nl sl I FNominal nr idr idsr (Some sr) :> FNominal nu idu idsu (Some su)
| IS_Nom             : forall (nl nr nu: bool) (idl idr idu: itype ftype) (idsl idsr idsu: list (itype ftype)) (sl sr su: option (stype ftype)),
    nl && nr >= nu -> cons idl idsl I cons idr idsr :> cons idu idsu -> sl I sr :> su ->
    FNominal nl idl idsl sl I FNominal nr idr idsr sr :> FNominal nu idu idsu su
(* with CommonSupertype_ident : itype ftype -> itype ftype -> itype ftype -> Prop := *)
| IS_Ident           : forall (name: string) (tal tar tau: list ftype), tal I tar :> tau -> It name tal I It name tar :> It name tau
(* with CommonSupertype_struct : stype ftype -> stype ftype -> stype ftype -> Prop := *)
| IS_Fn              : forall (tpl tpr tpu: list (tparam ftype)) (thispl thispr thispu: ftype)
                             (pl pr pu: list (otype ftype)) (rl rr ru: ftype) (retl retr retu: vtype ftype),
    tpl U tpr <: tpu -> thispl U thispr <: thispu -> pl U pr <: pu -> rl U rr <: ru -> retl I retr :> retu ->
    SFn tpl thispl pl rl retl I SFn tpr thispr pr rr retr :> SFn tpu thispu pu ru retu
| IS_Array           : forall (el er eu: ftype),                      el I er :> eu    -> SArray el   I SArray er   :> SArray eu
| IS_Tuple           : forall (esl esr esu: list (otype ftype)),      esl I esr :> esu -> STuple esl  I STuple esr  :> STuple esu
| IS_Object          : forall (fsl fsr fsu: js_record (otype ftype)), fsl I fsr :> fsu -> SObject fsl I SObject fsr :> SObject fsu
(* with CommonSupertype_otype : otype ftype -> otype ftype -> otype ftype -> Prop := *)
| IS_OType           : forall (ol or ou: bool) (lhs rhs uni: ftype), ol && or >= ou -> lhs I rhs :> uni -> Ot ol lhs I Ot or rhs :> Ot ou uni
(* with CommonSupertype_void : vtype ftype -> vtype ftype -> vtype ftype -> Prop := *)
| IS_Void            : @VVoid ftype I VVoid :> VVoid
| IS_NotVoid         : forall (lhs rhs uni: ftype), lhs I rhs :> uni -> Vt lhs I Vt rhs :> Vt uni
(* with CommonSupertype_tparam : tparam -> tparam -> tparam -> Prop := *)
| IS_TParam          : forall (vl vr vu: variance) (name: string) (supl supr supu: list ftype),
    vl I vr :> vu -> Supers_ supl I Supers_ supr :> Supers_ supu ->
    TParam vl name supl I TParam vr name supr :> TParam vu name supu
(* with CommonSupertype_zip_ftype : list ftype -> list ftype -> list ftype -> Prop := *)
| IS_NilFType        : @nil ftype I nil :> nil
| IS_ConsFType       : forall (xl xr xu: ftype) (xsl xsr xsu: list ftype),
    xl I xr :> xu -> xsl I xsr :> xsu -> cons xl xsl I cons xr xsr :> cons xu xsu
(* with CommonSupertype_zip_tparam : list tparam -> list tparam -> list tparam -> Prop := *)
| IS_NilTParam       : @nil (tparam ftype) I nil :> nil
| IS_ConsTParam     : forall (xl xr xu: tparam ftype) (xsl xsr xsu: list (tparam ftype)),
    xl I xr :> xu -> xsl I xsr :> xsu -> cons xl xsl I cons xr xsr :> cons xu xsu
(* with CommonSupertype_zip_otype : list (otype ftype) -> list (otype ftype) -> list (otype ftype) -> Prop := *)
| IS_OTypes          : forall (xsl xsr xsu: list (otype ftype)),
    Rev_ (List.rev xsl) I Rev_ (List.rev xsr) :> Rev_ (List.rev xsu) -> xsl I xsr :> xsu
(* with CommonSupertype_intersect_itype : list (itype ftype) -> list (itype ftype) -> list (itype ftype) -> Prop := *)
| IS_IntersectNil    : forall (idsu: list (itype ftype)), nil I nil :> idsu
| IS_IntersectConsL  : forall (idu: itype ftype) (idsl idsr idsu: list (itype ftype)), cons idu idsl I idsr :> cons idu idsu
| IS_IntersectConsR  : forall (idu: itype ftype) (idsl idsr idsu: list (itype ftype)), idsl I cons idu idsr :> cons idu idsu
| IS_IntersectInR    : forall (idl idr idu: itype ftype) (idsl idsr idsr' idsu: list (itype ftype)),
     List.Add idr idsr idsr' -> idl I idr :> idu -> idsl I idsr :> idsu -> cons idl idsl I idsr' :> cons idu idsu
| IS_IntersectInL    : forall (idl idr idu: itype ftype) (idsl idsr idsl' idsu: list (itype ftype)),
     List.Add idl idsl idsl' -> idl I idr :> idu -> idsl I idsr :> idsu -> idsl' I cons idr idsr :> cons idu idsu
(* with CommonSupertype_zip_otype_rev : Rev (list (otype ftype)) -> Rev (list (otype ftype)) -> Rev (list (otype ftype)) -> Prop := *)
| IS_NilOType        : Rev_ (@nil (otype ftype)) I Rev_ nil :> Rev_ nil
| IS_ConsOType       : forall (xl xr xu: otype ftype) (xsl xsr xsu: list (otype ftype)),
    xl I xr :> xu -> Rev_ xsl I Rev_ xsr :> Rev_ xsu -> Rev_ (cons xl xsl) I Rev_ (cons xr xsr) :> Rev_ (cons xu xsu)
| IS_ConsOTypeL      : forall (xsl xsr xsu: list (otype ftype)) (xu: otype ftype),
    Rev_ xsl I Rev_ xsr :> Rev_ xsu -> Rev_ (cons xu xsl) I Rev_ xsr :> Rev_ (cons xu xsu)
| IS_ConsOTypeR      : forall (xsl xsr xsu: list (otype ftype)) (xu: otype ftype),
    Rev_ xsl I Rev_ xsr :> Rev_ xsu -> Rev_ xsl I Rev_ (cons xu xsr) :> Rev_ (cons xu xsu)
| IS_ConsOTypeU      : forall (xsl xsr xsu: list (otype ftype)) (xu: otype ftype),
    Rev_ xsl I Rev_ xsr :> Rev_ xsu -> Rev_ xsl I Rev_ xsr :> Rev_ (cons xu xsu)
(* with CommonSupertype_intersect_ftype_supers : Supers (list ftype) -> Supers (list ftype) -> Supers (list ftype) -> Prop := *)
| IS_IntSupersNil    : Supers_ (@nil ftype) I Supers_ nil :> Supers_ nil
| IS_IntSupersConsL  : forall (xu: ftype) (xsl xsr xsu: list ftype), Supers_ (cons xu xsl) I Supers_ xsr :> Supers_ (cons xu xsu)
| IS_IntSupersConsR  : forall (xu: ftype) (xsl xsr xsu: list ftype), Supers_ xsl I Supers_ (cons xu xsr) :> Supers_ (cons xu xsu)
| IS_IntSupersConsU  : forall (xu: ftype) (xsl xsr xsu: list ftype), Supers_ xsl I Supers_ xsr :> Supers_ (cons xu xsu)
| IS_IntSupersInR    : forall (xl xr xu: ftype) (xsl xsr xsr' xsu: list ftype),
     List.Add xr xsr xsr' -> xl I xr :> xu -> xsl I xsr :> xsu -> Supers_ (cons xl xsl) I Supers_ xsr' :> Supers_ (cons xu xsu)
| IS_IntSupersInL    : forall (xl xr xu: ftype) (xsl xsr xsl' xsu: list ftype),
     List.Add xl xsl xsl' -> xl I xr :> xu -> xsl I xsr :> xsu -> Supers_ xsl' I Supers_ (cons xr xsr) :> Supers_ (cons xu xsu)
(* with CommonSupertype_js_record : js_record oftype -> js_record oftype -> js_record oftype -> Prop *)
| IS_JSNil           : @nil (string * ftype) I nil :> nil
| IS_JSInR           : forall (name: string) (vl vr vu: oftype) (vls vrs vrs' vus: js_record oftype),
    List.Add (name, vr) vrs vrs' -> vl I vr :> vu -> vls I vrs :> vus -> cons (name, vl) vls I vrs' :> cons (name, vu) vus
| IS_JSInL           : forall (name: string) (vl vr vu: oftype) (vls vls' vrs vus: js_record oftype),
    List.Add (name, vl) vls vls' -> vl I vr :> vu -> vls I vrs :> vus -> vls' I cons (name, vr) vrs :> cons (name, vu) vus
(* with CommonSupertype_variance : variance -> variance -> variance -> Prop *)
| IS_Invariant       : forall (lhs rhs: variance), lhs I rhs :> Invariant
| IS_Covariant       : Covariant I Covariant :> Covariant
| IS_Contravariant   : Contravariant I Contravariant :> Contravariant
| IS_BivariantL      : forall (rhs: variance), Bivariant I rhs :> rhs
| IS_BivariantR      : forall (lhs: variance), lhs I Bivariant :> lhs
where "a 'I' b :> c" := (CommonSubtype a b c)
.

Inductive HasVariance {A: Set} {h: HasRelation A} : A -> A -> variance -> Prop :=
| IsBivariant     : forall (lhs rhs uni: A), lhs U rhs <: uni -> HasVariance lhs rhs Bivariant
| IsCovariant     : forall (lhs rhs    : A), lhs U rhs <: rhs -> HasVariance lhs rhs Covariant
| IsContravariant : forall (lhs rhs    : A), lhs U rhs <: lhs -> HasVariance lhs rhs Contravariant
| IsInvariant     : forall (a          : A), a U a <: a       -> HasVariance a   a   Invariant
.

Definition IsSubtype {A: Set} {h: HasRelation A} (lhs rhs: A): Prop := lhs U rhs <: rhs.
Notation "lhs '<:' rhs" := (IsSubtype lhs rhs) (at level 63, no associativity).

Definition IsSupertype {A: Set} {h: HasRelation A} (lhs rhs: A): Prop := lhs I rhs :> rhs.
Notation "lhs ':>' rhs" := (IsSupertype lhs rhs) (at level 63, no associativity).

Definition IsBounded {A: Set} {h: HasRelation A} (x min max: A): Prop := min U x <: x /\ x U max <: max.
Notation "min '<:' x '<:' max" := (IsBounded x min max) (at level 64, no associativity).

Definition IsBoundedAlt {A: Set} {h: HasRelation A} (x min max: A): Prop := min I x :> min /\ x I max :> x.
Notation "max ':>' x ':>' min" := (IsBoundedAlt x min max) (at level 64, no associativity).

Definition Union {A: Set} {h: HasRelation A} (lhs rhs a: A): Prop := lhs U rhs <: a /\ forall b, lhs U rhs <: b -> a <: b.
Notation "lhs 'U' rhs '=' a" := (Union lhs rhs a) (at level 60, rhs at next level, no associativity).

Definition Intersect {A: Set} {h: HasRelation A} (lhs rhs a: A): Prop := lhs I rhs :> a /\ forall b, lhs I rhs :> b -> a :> b.
Notation "lhs 'I' rhs '=' a" := (Intersect lhs rhs a) (at level 60, rhs at next level, no associativity).

From TLC Require Import LibTactics.

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

Theorem subtype_refl: forall {A: Set} {h: HasRelation A} (a b: A), a <: b -> a <: a.
Admitted.

Theorem subtype_refl': forall (a: ftype), a <: a.
Admitted.
Local Hint Immediate subtype_refl'.

Theorem subtype_antisym: forall {A: Set} {h: HasRelation A} (a b: A), a <: b -> b :> a.
Admitted.

Theorem subtype_trans: forall {A: Set} {h: HasRelation A} (a b c: A), a <: b -> b <: c -> a <: c.
Admitted.

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

Theorem supertype_refl: forall {A: Set} {h: HasRelation A} (a b: A), a :> b -> a :> a.
Admitted.

Theorem supertype_antisym: forall {A: Set} {h: HasRelation A} (a b: A), a :> b -> b <: a.
Admitted.

Theorem supertype_trans: forall {A: Set} {h: HasRelation A} (a b c: A), a :> b -> b :> c -> a :> c.
Admitted.

Local Ltac by_contradiction H := contradiction H; fail.
Local Ltac clear_relation_neqs :=
  repeat match goal with
  | H : ?T1 = ?T2 |- _ => apply relation_type_eq1 in H; simpl in H; discriminate H
  end.
Local Ltac clear_obvious_eqs :=
  repeat lazymatch goal with
  | H : ?T = ?T |- _ => clear H
  end.

Ltac inv_cs H :=
  inverts H;
  try discriminate;
  clear_relation_neqs;
  clear_obvious_eqs.
Ltac discr_cs H := inv_cs H; fail.

Theorem union_never: forall (a: ftype), FNEVER U a = a.
Proof.
  intros. split.
  - apply US_NeverL.
  - intros. revert H. destruct a; destruct b; simpl; intros;
      try apply US_Any;
      try discr_cs H.
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

Local Ltac constructor' :=
  constructor + match goal with
  | |- context[(?x :: ?xs)%list] => destruct x; econstructor; [apply List.Add_head | |]
  | |- _ => fail "no constructor"
  end.

Local Ltac inv_ap0 Constr H t :=
  tryif apply Constr then (
    apply List.Forall_rev in H; remember (List.rev _) as t2 eqn:H0; clear H0;
      induction t2; inverts H; constructor
  ) else (
    induction' t; inverts H; constructor'; try discriminate
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
      + induction' b; try constructor;
          destruct nullable; destruct nullable0; simpl; try (reflexivity + inv_cs H0; inverts H1; inverts H2; inverts H3; simpl in H4; discriminate);
          inverts H.
        induction' structure0; try constructor. etc.

Theorem union_insersect_sym : forall {A: Set} {h: HasRelation A} (a b c: A),
    (a U b = c -> b U a = c) /\ (a I b = c -> b I a = c).
Admitted.

Theorem union_intersecttrans : forall {A: Set} {h: HasRelation A} (a b c x y z: A),
    (a U b = x -> b U c = y -> (a U c = z <-> x U y = z)) /\ (a I b = x -> b I c = y -> (a I c = z <-> x I y = z)).
Admitted.
