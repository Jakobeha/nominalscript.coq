
(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
From NS Require Import Misc.
From NS Require Import TypesBase.
From NS Require Import TypesNotation.
From NS Require Import TypesSimpleHelpers.

Local Notation "a < b" := (Bool.lt a b) : bool_scope.
Reserved Notation "a 'U' b '<:' c" (at level 60, b at next level, no associativity).
Reserved Notation "a 'U' b '<:2' c" (at level 60, b at next level, no associativity).
Inductive common_supertype : forall {A: Set}, A -> A -> A -> Prop :=
| CSAny             : forall (lhs rhs: ftype), lhs U rhs <: FAny
| CSNeverL          : forall (rhs: ftype), FNEVER U rhs <: rhs
| CSNeverR          : forall (lhs: ftype), lhs U FNEVER <: lhs
| CSNullL           : forall (rhs: ftype), IsNullable rhs -> FNULL U rhs <: rhs
| CSNullR           : forall (lhs: ftype), IsNullable lhs -> lhs U FNULL <: lhs
| CSStruct          : forall (nl nr nu: bool) (sl sr su: stype ftype),
    nl || nr < nu -> sl U sr <: su -> FStructural nl sl U FStructural nr sr <: FStructural nu su
| CSNomStruct       : forall (nl nr nu: bool) (idl: itype ftype) (idsl: list (itype ftype)) (sl sr su: stype ftype),
    nl || nr < nu -> sl U sr <: su -> FNominal nl idl idsl (Some sl) U FStructural nr sr <: FStructural nu su
| CSStructNom       : forall (nl nr nu: bool) (idr: itype ftype) (idsr: list (itype ftype)) (sl sr su: stype ftype),
    nl || nr < nu -> sl U sr <: su -> FStructural nl sl U FNominal nr idr idsr (Some sr) <: FStructural nu su
| CSNomCommonNom    : forall (nl nr nu: bool) (idl idr idu: itype ftype) (idsl idsr idsu: list (itype ftype)) (sl sr su: option (stype ftype)),
    nl || nr < nu -> cons idl idsl U cons idr idsr <: cons idu idsu -> sl U sr <: su ->
    FNominal nl idl idsl sl U FNominal nr idr idsr sr <: FNominal nu idu idsu su
| CSNomCommonStruct : forall (nl nr nu: bool) (idl idr: itype ftype) (idsl idsr: list (itype ftype)) (sl sr su: stype ftype),
    nl || nr < nu -> sl U sr <: su -> FNominal nl idl idsl (Some sl) U FNominal nr idr idsr (Some sr) <: FStructural nu su
(* with common_supertype_ident : itype ftype -> itype ftype -> itype ftype -> Prop := *)
| CSIdent           : forall (name: string) (tal tar tau: list ftype), tal U tar <: tau -> I name tal U I name tar <: I name tau
(* with common_supertype_struct : stype ftype -> stype ftype -> stype ftype -> Prop := *)
| CSFn              : forall (tpl tpr tpu: list (tparam ftype)) (thispl thispr thispu: ftype)
                             (pl pr pu: list (otype ftype)) (rl rr ru: ftype) (retl retr retu: vtype ftype),
    tpl U tpr <: tpu -> thispl U thispr <: thispu -> pl U pr <: pu -> rl U rr <: ru -> retl U retr <: retu ->
    SFn tpl thispl pl rl retl U SFn tpr thispr pr rr retr <: SFn tpu thispu pu ru retu
| CSArray           : forall (el er eu: ftype),                      el U er <: eu    -> SArray el   U SArray er   <: SArray eu
| CSTuple           : forall (esl esr esu: list (otype ftype)),      esl U esr <: esu -> STuple esl  U STuple esr  <: STuple esu
| CSObject          : forall (fsl fsr fsu: js_record (otype ftype)), fsl U fsr <: fsu -> SObject fsl U SObject fsr <: SObject fsu
(* with common_supertype_otype : otype ftype -> otype ftype -> otype ftype -> Prop := *)
| CSOType           : forall (ol or ou: bool) (lhs rhs uni: ftype), ol || or < ou -> lhs U rhs <: uni -> O ol lhs U O or rhs <: O ou uni
(* with common_supertype_void : vtype ftype -> vtype ftype -> vtype ftype -> Prop := *)
| CSVoid            : @VVoid ftype U VVoid <: VVoid
| CSNotVoid         : forall (lhs rhs uni: ftype), lhs U rhs <: uni -> V lhs U V rhs <: V uni
(* with common_supertype_zip_ftype : list ftype -> list ftype -> list ftype -> Prop := *)
| CSNilFType        : @nil ftype U nil <: nil
| CSConsFType       : forall (xl xr xu: ftype) (xsl xsr xsu: list ftype),
    xl U xr <: xu -> xsl U xsr <: xsu -> cons xl xsl U cons xr xsr <: cons xu xsu
(* with common_supertype_zip_otype : list (otype ftype) -> list (otype ftype) -> list (otype ftype) -> Prop := *)
| CSOTypes          : forall (xsl xsr xsu: list (otype ftype)), List.rev xsl U List.rev xsr <:2 List.rev xsu -> xsl U xsr <: xsu
(* with common_supertype_intersect_itype : list (itype ftype) -> list (itype ftype) -> list (itype ftype) -> Prop := *)
| CSIntersectNil    : forall (idsl idsr: list (itype ftype)), idsl U idsr <: nil
| CSIntersectConsL  : forall (idl: itype ftype) (idsl idsr idsu: list (itype ftype)), cons idl idsl U idsr <: idsu
| CSIntersectConsR  : forall (idr: itype ftype) (idsl idsr idsu: list (itype ftype)), idsl U cons idr idsr <: idsu
| CSIntersectInR    : forall (idl idr idu: itype ftype) (idsl idsr idsr' idsu: list (itype ftype)),
     List.Add idr idsr idsr' -> idl U idr <: idu -> cons idl idsl U idsr' <: cons idu idsu
| CSIntersectInL    : forall (idl idr idu: itype ftype) (idsl idsr idsl' idsu: list (itype ftype)),
     List.Add idl idsl idsl' -> idl U idr <: idu -> idsl' U cons idr idsr <: cons idu idsu
where "a 'U' b '<:' c" := (common_supertype a b c)
with common_supertype_zip_otype_rev : list (otype ftype) -> list (otype ftype) -> list (otype ftype) -> Prop :=
| CSNilOType        : nil U nil <:2 nil
| CSConsOType       : forall (xl xr xu: otype ftype) (xsl xsr xsu: list (otype ftype)),
    xl U xr <: xu -> xsl U xsr <:2 xsu -> cons xl xsl U cons xr xsr <:2 cons xu xsu
| CSConsOTypeL     : forall (xsl xsr xsu: list (otype ftype)) (xl: otype ftype), xsl U xsr <:2 xsu -> cons xl xsl U xsr <:2 xsu
| CSConsOTypeR     : forall (xsl xsr xsu: list (otype ftype)) (xr: otype ftype), xsl U xsr <:2 xsu -> xsl U cons xr xsr <:2 xsu
where "a 'U' b '<:2' c" := (common_supertype_zip_otype_rev a b c)
.

Inductive has_variance {A: Set} : A -> A -> variance -> Prop :=
| IsBivariant     : forall (lhs rhs uni: A), lhs U rhs <: uni -> has_variance lhs rhs Bivariant
| IsCovariant     : forall (lhs rhs    : A), lhs U rhs <: rhs -> has_variance lhs rhs Covariant
| IsContravariant : forall (lhs rhs    : A), lhs U rhs <: lhs -> has_variance lhs rhs Contravariant
| IsInvariant     : forall (a          : A), a U a <: a       -> has_variance a   a   Invariant
.

Definition is_subtype {A: Set} (lhs rhs: A): Prop := lhs U rhs <: rhs.
Notation "lhs '<:' rhs" := (is_subtype lhs rhs) (at level 63, no associativity).

Definition is_supertype {A: Set} (lhs rhs: A): Prop := lhs U rhs <: lhs.
Notation "lhs ':>' rhs" := (is_subtype lhs rhs) (at level 63, no associativity).

Definition is_bounded {A: Set} (x min max: A): Prop := min U x <: x /\ x U max <: x.
Notation "min '<:' x '<:' max" := (is_bounded x min max) (at level 64, no associativity).

Definition Union {A: Set} (lhs rhs a: A): Prop := lhs U rhs <: a /\ forall b, lhs U rhs <: b -> a <: b.
Notation "lhs 'U' rhs '=' a" := (Union lhs rhs a) (at level 63, rhs at next level, no associativity).

Theorem subtype_never: forall (a: ftype), FNEVER <: a.
Admitted.

Theorem subtype_null: forall (a: ftype), IsNullable a -> FNULL <: a.
Admitted.

Theorem subtype_any: forall (a: ftype), a <: FAny.
Admitted.

Theorem subtype_refl: forall {A: Set} (a b: A), a <: b -> a <: a.
Admitted.

Theorem subtype_antisym: forall {A: Set} (a b: A), a <: b -> b :> a.
Admitted.

Theorem subtype_trans: forall {A: Set} (a b c: A), a <: b -> b <: c -> a <: c.
Admitted.

Theorem supertype_never: forall (a: ftype), a :> FNEVER.
Admitted.

Theorem supertype_null: forall (a: ftype), IsNullable a -> a :> FNULL.
Admitted.

Theorem supertype_any: forall (a: ftype), FAny :> a.
Admitted.

Theorem supertype_refl: forall {A: Set} (a b: A), a :> b -> a :> a.
Admitted.

Theorem supertype_antisym: forall {A: Set} (a b: A), a :> b -> b <: a.
Admitted.

Theorem supertype_trans: forall {A: Set} (a b c: A), a :> b -> b :> c -> a :> c.
Admitted.

Theorem union_never: forall (a: ftype), FNEVER U a = a.
Admitted.

Theorem union_null: forall (a: ftype), IsNullable a -> FNULL U a = a.
Admitted.

Theorem union_any: forall (a: ftype), FAny U a = FAny.
Admitted.

Theorem union_refl : forall {A: Set} (a b c: A), a U b = c -> a U a = a.
Admitted.

Theorem union_sym : forall {A: Set} (a b c: A), a U b = c -> b U a = c.
Admitted.

Theorem union_trans : forall {A: Set} (a b c x y z: A), a U b = x -> b U c = y -> (a U c = z <-> x U y = z).
Admitted.
