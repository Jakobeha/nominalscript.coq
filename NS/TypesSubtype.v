(* -*- company-coq-local-symbols: (("U" . ?∪) ("I" . ?∩)); -*- *)
(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Add LoadPath "tlc/src" as TLC.
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

Create HintDb inv_con.

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

Inductive RelationType : Set :=
| ftype_RelationType
| itype_RelationType (_: RelationType)
| stype_RelationType (_: RelationType)
| otype_RelationType (_: RelationType)
| vtype_RelationType (_: RelationType)
| tparam_RelationType (_: RelationType)
| variance_RelationType
| option_RelationType (_: RelationType)
| Zip_RelationType (_: RelationType)
| JsrZip_RelationType (_: RelationType)
| Intersect_RelationType (_: RelationType)
.
Class HasRelation (A: Set) := { relation_type : RelationType }.
Global Instance ftype_HasRelation : HasRelation ftype := { relation_type := ftype_RelationType }.
Global Instance itype_HasRelation : forall {A: Set} {h: HasRelation A}, HasRelation (itype A) := { relation_type := itype_RelationType (@relation_type A h) }.
Global Instance stype_HasRelation : forall {A: Set} {h: HasRelation A}, HasRelation (stype A) := { relation_type := stype_RelationType (@relation_type A h) }.
Global Instance otype_HasRelation : forall {A: Set} {h: HasRelation A}, HasRelation (otype A) := { relation_type := otype_RelationType (@relation_type A h) }.
Global Instance vtype_HasRelation : forall {A: Set} {h: HasRelation A}, HasRelation (vtype A) := { relation_type := vtype_RelationType (@relation_type A h) }.
Global Instance tparam_HasRelation : forall {A: Set} {h: HasRelation A}, HasRelation (tparam A) := { relation_type := tparam_RelationType (@relation_type A h) }.
Global Instance variance_HasRelation : HasRelation variance := { relation_type := variance_RelationType }.
Global Instance option_HasRelation : forall {A: Set} {h: HasRelation A}, HasRelation (option A) := { relation_type := option_RelationType (@relation_type A h) }.
Global Instance Zip_HasRelation : forall {A: Set} {h: HasRelation A}, HasRelation (Zip A) := { relation_type := Zip_RelationType (@relation_type A h) }.
Global Instance JsrZip_HasRelation : forall {A: Set} {h: HasRelation A}, HasRelation (JsrZip A) := { relation_type := JsrZip_RelationType (@relation_type A h) }.
Global Instance Intersect_HasRelation : forall {A: Set} {h: HasRelation A}, HasRelation (Intersect A) := { relation_type := Intersect_RelationType (@relation_type A h) }.
Set Warnings "-fragile-hint-constr".
Global Hint Resolve ftype_HasRelation : inv_con.
Global Hint Resolve itype_HasRelation : inv_con.
Global Hint Resolve stype_HasRelation : inv_con.
Global Hint Resolve otype_HasRelation : inv_con.
Global Hint Resolve vtype_HasRelation : inv_con.
Global Hint Resolve tparam_HasRelation : inv_con.
Global Hint Resolve variance_HasRelation : inv_con.
Global Hint Resolve option_HasRelation : inv_con.
Global Hint Resolve Zip_HasRelation : inv_con.
Global Hint Resolve JsrZip_HasRelation : inv_con.
Global Hint Resolve Intersect_HasRelation : inv_con.
Set Warnings "+fragile-hint-constr".
Axiom relation_type_eq: forall {A B: Set} {hA: HasRelation A} {hB: HasRelation B},
    A = B <-> @relation_type A hA = @relation_type B hB.
Ltac discr_relation_eqs :=
  try (rewrite relation_type_eq in *; discriminate).
Global Hint Extern 2 => discr_relation_eqs : inv_con.
Axiom HasRelation_existT : forall {A B: Set} {hA: HasRelation A} {hB: HasRelation B} {a: A} {b: B},
  existT (fun x0 : Set => x0) A a = existT (fun x1 : Set => x1) B b ->
  A = B /\ a ~= b.
Ltac remove_hasRelation_existTs :=
  repeat lazymatch goal with
  | H : existT (fun x0 : Set => x0) ?A ?a = existT (fun x1 : Set => x1) ?B ?b |- _ => apply HasRelation_existT in H; destruct H
  end.
Locate JMeq.
Local Ltac inv_no_subst H :=
  inversion H;
  remove_existTs;
  remove_hasRelation_existTs;
  injections;
  discr_relation_eqs;
  clear_obvious;
  simpl_JMeq;
  clear H;
  try discriminate.
Local Ltac inv H :=
  inversion H;
  remove_existTs;
  remove_hasRelation_existTs;
  injections;
  discr_relation_eqs;
  subst;
  clear_obvious;
  simpl_JMeq;
  clear H;
  try discriminate.
Ltac inv_cs H := inv H.

Local Open Scope list_scope.
Local Notation "a <= b" := (Bool.le a b) : bool_scope.
Local Notation "a >= b" := (Bool.le b a) : bool_scope.
Reserved Notation "'(U <:)'".
Reserved Notation "'(I :>)'".
Reserved Notation "a 'U' b '<:' c" (at level 60, b at next level, no associativity).
Reserved Notation "a 'I' b ':>' c" (at level 60, b at next level, no associativity).
Reserved Notation "a 'Zip-U' b '<:' c" (at level 60, b at next level, no associativity).
Reserved Notation "a 'Zip-I' b ':>' c" (at level 60, b at next level, no associativity).
Reserved Notation "a 'JsrZip-U' b '<:' c" (at level 60, b at next level, no associativity).
Reserved Notation "a 'JsrZip-I' b ':>' c" (at level 60, b at next level, no associativity).
Reserved Notation "a 'Intersect-U' b '<:' c" (at level 60, b at next level, no associativity).
Reserved Notation "a 'Intersect-I' b ':>' c" (at level 60, b at next level, no associativity).
Inductive CommonSupertype : forall {A: Set} {h: HasRelation A}, A -> A -> A -> Prop :=
| US_Any             : forall (lhs rhs: ftype), lhs U rhs <: FAny
| US_Never           : forall (a: ftype), FNEVER U FNEVER <: a
| US_NeverL          : forall (rhs: ftype), FNEVER U rhs <: rhs
| US_NeverR          : forall (lhs: ftype), lhs U FNEVER <: lhs
| US_Null            : forall (a: ftype), IsNullable a -> FNULL U FNULL <: a
| US_NullL           : forall (rhs: ftype), IsNullable rhs -> FNULL U rhs <: rhs
| US_NullR           : forall (lhs: ftype), IsNullable lhs -> lhs U FNULL <: lhs
| US_NeverNull       : FNEVER U FNEVER <: FNULL
| US_Struct          : forall (nl nr nu: bool) (sl sr su: sftype),
    nl || nr <= nu -> sl U sr <: su -> FStructural nl sl U FStructural nr sr <: FStructural nu su
| US_NomStruct       : forall (nl nr nu: bool) (idl: iftype) (idsl: list iftype) (sl sr su: sftype),
    nl || nr <= nu -> sl U sr <: su -> FNominal nl idl idsl (Some sl) U FStructural nr sr <: FStructural nu su
| US_StructNom       : forall (nl nr nu: bool) (idr: iftype) (idsr: list iftype) (sl sr su: sftype),
    nl || nr <= nu -> sl U sr <: su -> FStructural nl sl U FNominal nr idr idsr (Some sr) <: FStructural nu su
| US_NomCommonNom    : forall (nl nr nu: bool) (idl idr idu: iftype) (idsl idsr idsu: list iftype) (sl sr su: option sftype),
    nl || nr <= nu -> (idl :: idsl) Intersect-U (idr :: idsr) <: (idu :: idsu) -> sl U sr <: su ->
    FNominal nl idl idsl sl U FNominal nr idr idsr sr <: FNominal nu idu idsu su
| US_NomCommonStruct : forall (nl nr nu: bool) (idl idr: iftype) (idsl idsr: list iftype) (sl sr su: sftype),
    nl || nr <= nu -> sl U sr <: su -> FNominal nl idl idsl (Some sl) U FNominal nr idr idsr (Some sr) <: FStructural nu su
(* with CommonSupertype_ident : iftype -> iftype -> iftype -> Prop := *)
| US_Ident           : forall (name: string) (tal tar tau: list ftype), tal Zip-U tar <: tau -> It name tal U It name tar <: It name tau
(* with CommonSupertype_struct : sftype -> sftype -> sftype -> Prop := *)
| US_Fn              : forall (tpl tpr tpu: list ftparam) (thispl thispr thispu: ftype)
                         (pl pr pu: list oftype) (rl rr ru: ftype) (retl retr retu: vftype),
    tpl Zip-I tpr :> tpu -> thispl I thispr :> thispu -> pl Zip-I pr :> pu -> rl I rr :> ru -> retl U retr <: retu ->
    SFn tpl thispl pl rl retl U SFn tpr thispr pr rr retr <: SFn tpu thispu pu ru retu
| US_Array           : forall (el er eu: ftype),               el         U er  <: eu  -> SArray el   U SArray er   <: SArray eu
| US_Tuple           : forall (esl esr esu: list oftype),      esl    Zip-U esr <: esu -> STuple esl  U STuple esr  <: STuple esu
| US_Object          : forall (fsl fsr fsu: js_record oftype), fsl JsrZip-U fsr <: fsu -> SObject fsl U SObject fsr <: SObject fsu
(* with CommonSupertype_otype : oftype -> oftype -> oftype -> Prop := *)
| US_OType           : forall (ol or ou: bool) (lhs rhs uni: ftype), ol || or <= ou -> lhs U rhs <: uni -> Ot ol lhs U Ot or rhs <: Ot ou uni
(* with CommonSupertype_void : vftype -> vftype -> vftype -> Prop := *)
| US_Void            : @VVoid ftype U VVoid <: VVoid
| US_NotVoid         : forall (lhs rhs uni: ftype), lhs U rhs <: uni -> Vt lhs U Vt rhs <: Vt uni
(* with CommonSupertype_tparam : ftparam -> ftparam -> ftparam -> Prop := *)
| US_TParam          : forall (vl vr vu: variance) (name: string) (supl supr supu: list ftype),
    vl U vr <: vu -> supl Intersect-U supr <: supu ->
    TParam vl name supl U TParam vr name supr <: TParam vu name supu
(* with CommonSupertype_variance : variance -> variance -> variance -> Prop *)
| US_Bivariant       : forall (lhs rhs: variance), lhs U rhs <: Bivariant
| US_Covariant       : Covariant U Covariant <: Covariant
| US_Contravariant   : Contravariant U Contravariant <: Contravariant
| US_InvariantL      : forall (rhs: variance), Invariant U rhs <: rhs
| US_InvariantR      : forall (lhs: variance), lhs U Invariant <: lhs
(* with CommonSupertype_opt : option A -> option A -> option A -> Prop := *)
| US_None            : forall {A: Set} {h: HasRelation A} (lhs rhs: option A), lhs U rhs <: None
| US_Some            : forall {A: Set} {h: HasRelation A} (lhs rhs uni: A), lhs U rhs <: uni -> Some lhs U Some rhs <: Some uni
(* Zip *)
| US_Zip_nil_r       : forall {A: Set} {h: HasRelation A} (lhs: list A), lhs Zip-U nil <: lhs
| US_Zip_nil_l       : forall {A: Set} {h: HasRelation A} (rhs: list A), nil Zip-U rhs <: rhs
| US_Zip_cons        : forall {A: Set} {h: HasRelation A} (l r u: A) (ls rs us: list A),
    l U r <: u -> ls Zip-U rs <: us -> (l :: ls) Zip-U (r :: rs) <: (u :: us)
(* JsrZip *)
| US_JsrZip_nil_r    : forall {A: Set} {h: HasRelation A} (lhs: js_record A), lhs JsrZip-U nil <: lhs
| US_JsrZip_nil_l    : forall {A: Set} {h: HasRelation A} (rhs: js_record A), nil JsrZip-U rhs <: rhs
| US_JsrZip_cons_l   : forall {A: Set} {h: HasRelation A} (k: string) (vl vr vu: A) (ls rs rs' us: js_record A),
    vl U vr <: vu -> JsRecordAdd k vr rs rs' -> ((k, vl) :: ls) JsrZip-U rs' <: ((k, vu) :: us)
| US_JsrZip_cons_r   : forall {A: Set} {h: HasRelation A} (k: string) (vl vr vu: A) (ls ls' rs us: js_record A),
    vl U vr <: vu -> JsRecordAdd k vl ls ls' -> ls' JsrZip-U ((k, vr) :: rs) <: ((k, vu) :: us)
| US_JsrZip_cons_u   : forall {A: Set} {h: HasRelation A} (k: string) (vl vr vu: A) (ls rs us us': js_record A),
    vl U vr <: vu -> JsRecordAdd k vu us us' -> ((k, vl) :: ls) JsrZip-U ((k, vr) :: rs) <: us'
(* Intersect *)
| US_Intersect_nil_r : forall {A: Set} {h: HasRelation A} (lhs: list A), lhs Intersect-U nil <: lhs
| US_Intersect_nil_l : forall {A: Set} {h: HasRelation A} (rhs: list A), nil Intersect-U rhs <: rhs
| US_Intersect_cons_l: forall {A: Set} {h: HasRelation A} (l r u: A) (ls rs rs' us: list A),
    l U r <: u -> List.Add r rs rs' -> (l :: ls) Intersect-U rs' <: (u :: us)
| US_Intersect_cons_r: forall {A: Set} {h: HasRelation A} (l r u: A) (ls ls' rs us: list A),
    l U r <: u -> List.Add l ls ls' -> ls' Intersect-U (r :: rs) <: (u :: us)
| US_Intersect_cons_u: forall {A: Set} {h: HasRelation A} (l r u: A) (ls rs us us': list A),
    l U r <: u -> List.Add u us us' -> (l :: ls) Intersect-U (r :: rs) <: us'
where "'(U <:)'" := CommonSupertype
  and "a 'U' b '<:' c" := (CommonSupertype a b c)
  and "a 'Zip-U' b '<:' c" := (CommonSupertype (Zip_ a) (Zip_ b) (Zip_ c))
  and "a 'JsrZip-U' b '<:' c" := (CommonSupertype (JsrZip_ a) (JsrZip_ b) (JsrZip_ c))
  and "a 'Intersect-U' b '<:' c" := (CommonSupertype (Intersect_ a) (Intersect_ b) (Intersect_ c))
with CommonSubtype : forall {A: Set}, A -> A -> A -> Prop :=
| IS_Never           : forall (lhs rhs: ftype), lhs I rhs :> FNEVER
| IS_Null            : forall (lhs rhs: ftype), IsNullable lhs -> IsNullable rhs -> lhs I rhs :> FNULL
| IS_AnyL            : forall (rhs: ftype), FAny I rhs :> rhs
| IS_AnyR            : forall (lhs: ftype), lhs I FAny :> lhs
| IS_Struct          : forall (nl nr nu: bool) (sl sr su: sftype),
    nl && nr >= nu -> sl I sr :> su -> FStructural nl sl I FStructural nr sr :> FStructural nu su
| IS_NomStruct       : forall (nl nr nu: bool) (idl idu: iftype) (idsl idsu: list iftype) (sl sr su: sftype),
    nl && nr >= nu -> (idl :: idsl) Intersect-I nil :> (idu :: idsu) -> sl I sr :> su ->
    FNominal nl idl idsl (Some sl) I FStructural nr sr :> FNominal nu idu idsu (Some su)
| IS_StructNom       : forall (nl nr nu: bool) (idr idu: iftype) (idsr idsu: list iftype) (sl sr su: sftype),
    nl && nr >= nu -> nil Intersect-I (idr :: idsr) :> (idu :: idsu) -> sl I sr :> su ->
    FStructural nl sl I FNominal nr idr idsr (Some sr) :> FNominal nu idu idsu (Some su)
| IS_Nom             : forall (nl nr nu: bool) (idl idr idu: iftype) (idsl idsr idsu: list iftype) (sl sr su: option sftype),
    nl && nr >= nu -> (idl :: idsl) Intersect-I (idr :: idsr) :> (idu :: idsu) -> sl I sr :> su ->
    FNominal nl idl idsl sl I FNominal nr idr idsr sr :> FNominal nu idu idsu su
(* with CommonSupertype_ident : iftype -> iftype -> iftype -> Prop := *)
| IS_Ident           : forall (name: string) (tal tar tau: list ftype), tal Zip-I tar :> tau -> It name tal I It name tar :> It name tau
(* with CommonSupertype_struct : sftype -> sftype -> sftype -> Prop := *)
| IS_Fn              : forall (tpl tpr tpu: list (ftparam)) (thispl thispr thispu: ftype)
                             (pl pr pu: list (oftype)) (rl rr ru: ftype) (retl retr retu: vftype),
    tpl Zip-U tpr <: tpu -> thispl U thispr <: thispu -> pl Zip-U pr <: pu -> rl U rr <: ru -> retl I retr :> retu ->
    SFn tpl thispl pl rl retl I SFn tpr thispr pr rr retr :> SFn tpu thispu pu ru retu
| IS_Array           : forall (el er eu: ftype),               el         I er  :> eu  -> SArray el   I SArray er   :> SArray eu
| IS_Tuple           : forall (esl esr esu: list oftype),      esl    Zip-I esr :> esu -> STuple esl  I STuple esr  :> STuple esu
| IS_Object          : forall (fsl fsr fsu: js_record oftype), fsl JsrZip-I fsr :> fsu -> SObject fsl I SObject fsr :> SObject fsu
(* with CommonSupertype_otype : oftype -> oftype -> oftype -> Prop := *)
| IS_OType           : forall (ol or ou: bool) (lhs rhs uni: ftype), ol && or >= ou -> lhs I rhs :> uni -> Ot ol lhs I Ot or rhs :> Ot ou uni
(* with CommonSupertype_void : vftype -> vftype -> vftype -> Prop := *)
| IS_Void            : @VVoid ftype I VVoid :> VVoid
| IS_NotVoid         : forall (lhs rhs uni: ftype), lhs I rhs :> uni -> Vt lhs I Vt rhs :> Vt uni
(* with CommonSupertype_tparam : ftparam -> ftparam -> ftparam -> Prop := *)
| IS_TParam          : forall (vl vr vu: variance) (name: string) (supl supr supu: list ftype),
    vl I vr :> vu -> supl Intersect-I supr :> supu ->
    TParam vl name supl I TParam vr name supr :> TParam vu name supu
(* with CommonSupertype_variance : variance -> variance -> variance -> Prop *)
| IS_Invariant       : forall (lhs rhs: variance), lhs I rhs :> Invariant
| IS_Covariant       : Covariant I Covariant :> Covariant
| IS_Contravariant   : Contravariant I Contravariant :> Contravariant
| IS_Bivariant       : forall (a: variance), Bivariant I Bivariant :> a
| IS_BivariantL      : forall (rhs: variance), Bivariant I rhs :> rhs
| IS_BivariantR      : forall (lhs: variance), lhs I Bivariant :> lhs
(* with CommonSubtype_opt : option A -> option A -> option A -> Prop := *)
| IS_NoneNone        : forall {A: Set} {h: HasRelation A} (uni: option A), None I None :> uni
| IS_NoneSome        : forall {A: Set} {h: HasRelation A} (lhs: A), Some lhs I None :> Some lhs
| IS_SomeNone        : forall {A: Set} {h: HasRelation A} (rhs: A), None I Some rhs :> Some rhs
| IS_SomeSome        : forall {A: Set} {h: HasRelation A} (lhs rhs uni: A), lhs I rhs :> uni -> Some lhs I Some rhs :> Some uni
(* Zip *)
| IS_Zip_nil         : forall {A: Set} {h: HasRelation A} (uni: list A), nil Zip-I nil :> uni
| IS_Zip_cons        : forall {A: Set} {h: HasRelation A} (l r u: A) (ls rs us: list A),
    l I r :> u -> ls Zip-I rs :> us -> (l :: ls) Zip-I (r :: rs) :> (u :: us)
(* JsrZip *)
| IS_JsrZip_nil      : forall {A: Set} {h: HasRelation A} (uni: js_record A), nil JsrZip-I nil :> uni
| IS_JsrZip_cons_l   : forall {A: Set} {h: HasRelation A} (k: string) (vl vr vu: A) (ls rs rs' us: js_record A),
    vl I vr :> vu -> JsRecordAdd k vr rs rs' -> ((k, vl) :: ls) JsrZip-I rs' :> ((k, vu) :: us)
| IS_JsrZip_cons_r   : forall {A: Set} {h: HasRelation A} (k: string) (vl vr vu: A) (ls ls' rs us: js_record A),
    vl I vr :> vu -> JsRecordAdd k vl ls ls' -> ls' JsrZip-I ((k, vr) :: rs) :> ((k, vu) :: us)
| IS_JsrZip_cons_u   : forall {A: Set} {h: HasRelation A} (k: string) (vl vr vu: A) (ls rs us us': js_record A),
    vl I vr :> vu -> JsRecordAdd k vu us us' -> ((k, vl) :: ls) JsrZip-I ((k, vr) :: rs) :> us'
(* Intersect *)
| IS_Intersect_nil   : forall {A: Set} {h: HasRelation A} (uni: list A), nil Intersect-I nil :> uni
| IS_Intersect_cons_l: forall {A: Set} {h: HasRelation A} (l r u: A) (ls rs rs' us: list A),
    l I r :> u -> List.Add r rs rs' -> (l :: ls) Intersect-I rs' :> (u :: us)
| IS_Intersect_cons_r: forall {A: Set} {h: HasRelation A} (l r u: A) (ls ls' rs us: list A),
    l I r :> u -> List.Add l ls ls' -> ls' Intersect-I (r :: rs) :> (u :: us)
| IS_Intersect_cons_u: forall {A: Set} {h: HasRelation A} (l r u: A) (ls rs us us': list A),
    l I r :> u -> List.Add u us us' -> (l :: ls) Intersect-I (r :: rs) :> us'
where "'(I :>)'" := CommonSubtype
  and "a 'I' b :> c" := (CommonSubtype a b c)
  and "a 'Zip-I' b ':>' c" := (CommonSubtype (Zip_ a) (Zip_ b) (Zip_ c))
  and "a 'JsrZip-I' b ':>' c" := (CommonSubtype (JsrZip_ a) (JsrZip_ b) (JsrZip_ c))
  and "a 'Intersect-I' b ':>' c" := (CommonSubtype (Intersect_ a) (Intersect_ b) (Intersect_ c))
.

Inductive HasVariance {A: Set} {h: HasRelation A} : A -> A -> variance -> Prop :=
| IsBivariant     : forall (lhs rhs uni: A), lhs U rhs <: uni -> HasVariance lhs rhs Bivariant
| IsCovariant     : forall (lhs rhs    : A), lhs U rhs <: rhs -> HasVariance lhs rhs Covariant
| IsContravariant : forall (lhs rhs    : A), lhs U rhs <: lhs -> HasVariance lhs rhs Contravariant
| IsInvariant     : forall (a          : A), a U a <: a       -> HasVariance a   a   Invariant
.

Definition IsSubtype {A: Set} {h: HasRelation A} (lhs rhs: A): Prop := lhs U rhs <: rhs.
Notation "'(<:)'" := IsSubtype.
Notation "lhs '<:' rhs" := (IsSubtype lhs rhs) (at level 63, no associativity).

Definition IsSupertype {A: Set} {h: HasRelation A} (lhs rhs: A): Prop := lhs I rhs :> rhs.
Notation "'(:>)'" := IsSupertype.
Notation "lhs ':>' rhs" := (IsSupertype lhs rhs) (at level 63, no associativity).

Definition IsBounded {A: Set} {h: HasRelation A} (x min max: A): Prop := min U x <: x /\ x U max <: max.
Notation "min '<:' x '<:' max" := (IsBounded x min max) (at level 64, no associativity).

Definition IsBoundedAlt {A: Set} {h: HasRelation A} (x min max: A): Prop := min I x :> min /\ x I max :> x.
Notation "max ':>' x ':>' min" := (IsBoundedAlt x min max) (at level 64, no associativity).

Definition Union {A: Set} {h: HasRelation A} (lhs rhs a: A): Prop := lhs U rhs <: a /\ forall b, lhs U rhs <: b -> a <: b.
Notation "'(U)'" := Union.
Notation "lhs 'U' rhs '=' a" := (Union lhs rhs a) (at level 60, rhs at next level, no associativity).

Definition Intersection {A: Set} {h: HasRelation A} (lhs rhs a: A): Prop := lhs I rhs :> a /\ forall b, lhs I rhs :> b -> a :> b.
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

Local Ltac ind2 a b :=
  lazymatch type of a with
  | js_record _ => induction2 a b using ind_js_record2
  | list _ => induction2 a b using ind_list2
  | _ => destruct a; destruct b
  end.

Local Ltac ind_cs a b c :=
  lazymatch constr:((a, b, c)) with
  | (?a, ?a, ?a) => ind1 a
  | (?a, ?b, ?b) => ind2 a b
  | (?b, ?a, ?b) => ind2 b a
  | (?a, ?b, ?c) => ind1 c
  end.

Local Ltac constr_eq_any3 d a b c :=
  first [constr_eq_strict d a | constr_eq_strict d b | constr_eq_strict d c].

Local Ltac constr_eq_any33 d e f a b c :=
  first [constr_eq_any3 d a b c | constr_eq_any3 e a b c | constr_eq_any3 f a b c].

Local Ltac inv_con2 a b c :=
  let CS := fresh "CS" in let Inv := fresh "Inv" in
  match goal with
  | CS' : ?d U ?e <: ?f |- _ => constr_eq_any33 d e f a b c; rename CS' into CS
  | CS' : ?d I ?e :> ?f |- _ => constr_eq_any33 d e f a b c; rename CS' into CS
  | _ => idtac
  end;
  match goal with
  | Inv' : ?P ?d |- _ => assert_fails (constr_eq_strict Inv' CS); constr_eq_any3 d a b c; rename Inv' into Inv
  | _ => idtac
  end;
  once (ind_cs a b c; try (inv Inv); try (inv_cs CS));
  try constructor; invert_eqs; simpl; try (reflexivity || discriminate).

Local Ltac is_var' a := first [is_var a | is_evar a].

Local Ltac inv_con1 a b c :=
  tryif is_var' a; is_var' b; is_var' c then inv_con2 a b c else fail "tried to inv_con non-variables".

Local Ltac inv_con_guard_type P :=
  lazymatch P with
  | JsrZip_ => fail
  | Intersect_ => fail
  | _ => idtac
  end.

Local Ltac inv_con0 a b c :=
  lazymatch constr:((a, b, c)) with
  (* Special cases *)
  | (FAny, _, _) => constructor || fail "subtype is stuck on FAny"
  | (_, FAny, _) => constructor || fail "subtype is stuck on FAny"
  | (_, _, FAny) => constructor || fail "subtype is stuck on FAny"
  | (?a, ?b, FStructural ?nullable _) => inv_con2 a b nullable
  | (?a, ?b, FNominal ?nullable _ _ _) => inv_con2 a b nullable
  (* General cases *)
  | (?P ?a, ?P ?b, ?P ?c) => first [inv_con_guard_type P | fail "type is special-cased"]; inv_con1 a b c
  | (?a, ?b, ?c) => inv_con1 a b c
  end.

Ltac first_inv_con a :=
  induction a using ftype_rec'; intros; split; intros; unfold IsSubtype, IsSupertype in *.

Local Ltac post_inv_con_hook := idtac.

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
  (* Boolean cases *)
  | |- ?n0 && ?n1 >= ?n2 => ind_cs n0 n1 n2; simpl; reflexivity || discriminate || fail "bad boolean equality"
  | |- ?n0 || ?n1 <= ?n2 => ind_cs n0 n1 n2; simpl; reflexivity || discriminate || fail "bad boolean equality"
  | |- ?n0 && ?n1 = ?n2 => ind_cs n0 n1 n2; simpl; reflexivity || discriminate || fail "badf boolean equality"
  | |- IsNullable ?P => simpl; reflexivity || fail "bad IsNullable"
  | |- Is_true ?nullable => destruct nullable; reflexivity || discriminate || fail "bad Is_true"
  | |- _ => post_inv_con_hook
  end; auto with inv_con.

(* Destruct or induct on goal, invert dependent hypotheses, apply the corresponding constructor *)
Local Ltac inv_con :=
  lazymatch goal with
  | |- ?a I ?b :> ?c => inv_con0 a b c
  | |- ?a U ?b <: ?c => inv_con0 a b c
  | |- _ => fail "not inv_con supported"
  end; post_inv_con.

Local Ltac inv_con' := repeat progress inv_con.

Local Ltac post_inv_con_hook ::=
  lazymatch goal with
  | G : forall (a: ftype), a I a :> a /\ a U a <: a |- ?a I ?a :> ?a => specialize (G a); destruct G as [G _]; exact G || fail "mismatched inductive end-case"
  | G : forall (a: ftype), a I a :> a /\ a U a <: a |- ?a U ?a <: ?a => specialize (G a); destruct G as [_ G]; exact G || fail "mismatched inductive end-case"
  | |- _ => idtac
  end.

Theorem subtype_supertype_refl: forall (a: ftype), a :> a /\ a <: a.
Proof with inv_con'.
  first_inv_con a...
  all: tryif is_var supers then induction supers; [constructor; auto with inv_con |]; match goal with H: List.Forall _ (_ :: _)%list |- _ => inv H end; unshelve (eapply IS_Intersect_cons_u || eapply US_Intersect_cons_u);
      [exact a | | | apply List.Add_head]; post_inv_con else idtac.
  all: tryif is_var fields then induction fields; [constructor; auto with inv_con |]; match goal with H: JsRecordForall _ _ |- _ => inv H end; destruct a as [kx vx]; unshelve (eapply IS_JsrZip_cons_u || eapply US_JsrZip_cons_u);
      [exact vx | | match goal with H: OType_Forall _ _ |- _ => simpl in H end | apply JsRecordAdd_head]; inv_con' else idtac.
  all: unshelve (econstructor; auto with inv_con); [exact id | | match goal with H : IType_Forall _ _ |- _ => inv H end; constructor | apply List.Add_head]...
Qed.

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
