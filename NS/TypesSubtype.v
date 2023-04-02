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
Definition SubtypeRelation (A: Set) := relation A.
Definition ap_SubtypeRelation {A: Set} (S: SubtypeRelation A) (lhs rhs: A) := S lhs rhs.
Class SubtypeOf (A: Set) := Subtype : SubtypeRelation A.
Notation "'[' Subtype ']' lhs '<:' rhs" := (ap_SubtypeRelation Subtype lhs rhs) (at level 60, lhs at next level, rhs at next level, no associativity).
Notation "'[' Subtype ']' lhs ':>' rhs" := (ap_SubtypeRelation Subtype rhs lhs) (at level 60, lhs at next level, rhs at next level, no associativity).
Notation "lhs '<:' rhs" := (Subtype lhs rhs) (at level 60, rhs at next level, no associativity).
Notation "lhs ':>' rhs" := (Subtype rhs lhs) (at level 60, rhs at next level, no associativity).
(* with CommonSupertype_opt : option A -> option A -> option A -> Prop := *)
Inductive S_option {A: Set} (S: SubtypeRelation A) : SubtypeRelation (option A) :=
| S_None            : forall (lhs: option A), [S_option S] lhs <: None
| S_Some            : forall (lhs rhs: A), [S] lhs <: rhs -> [S_option S] Some lhs <: Some rhs
.
Global Instance SOf_option {A: Set} {S: SubtypeOf A} : SubtypeOf (option A) := S_option S.
Inductive S_Zip {A: Set} (S: SubtypeRelation A) : SubtypeRelation (list A) :=
| S_Zip_nil          : forall (lhs: list A), [S_Zip S] lhs <: nil
| S_Zip_cons         : forall (l r: A) (ls rs: list A),
    [S] l <: r -> [S_Zip S] ls <: rs -> [S_Zip S] (l :: ls) <: (r :: rs)
.
Inductive S_JsrZip {A: Set} (S: SubtypeRelation A) : SubtypeRelation (js_record A) :=
| S_JsrZip_nil       : forall (lhs: js_record A), [S_JsrZip S] lhs <: nil
| S_JsrZip_cons_l    : forall (k: string) (vl vr: A) (ls rs rs': js_record A),
    [S] vl <: vr -> [S_JsrZip S] ls <: rs -> JsRecordAdd k vr rs rs' -> [S_JsrZip S] ((k, vl) :: ls) <: rs'
| S_JsrZip_cons_r    : forall (k: string) (vl vr: A) (ls ls' rs: js_record A),
    [S] vl <: vr -> [S_JsrZip S] ls <: rs -> JsRecordAdd k vl ls ls' -> [S_JsrZip S] ls' <: ((k, vr) :: rs)
.
Inductive S_Intersect {A: Set} (S: SubtypeRelation A) : SubtypeRelation (list A) :=
| S_Intersect_nil    : forall (lhs: list A), [S_Intersect S] lhs <: nil
| S_Intersect_cons_l : forall (l r: A) (ls rs rs': list A),
    [S] l <: r -> [S_Intersect S] ls <: rs -> List.Add r rs rs' -> [S_Intersect S] (l :: ls) <: rs'
| S_Intersect_cons_r : forall (l r: A) (ls ls' rs: list A),
    [S] l <: r -> [S_Intersect S] ls <: rs -> List.Add l ls ls' -> [S_Intersect S] ls' <: (r :: rs)
.
Inductive S_variance : SubtypeRelation variance :=
| S_Bivariant        : forall (lhs: variance), [S_variance] lhs <: Bivariant
| S_Covariant        : [S_variance] Covariant <: Covariant
| S_Contravariant    : [S_variance] Contravariant <: Contravariant
| S_Invariant        : forall (rhs: variance), [S_variance] Invariant <: rhs
.
Global Instance SOf_variance : SubtypeOf variance := S_variance.
Inductive S_otype {A: Set} (S: SubtypeRelation A) : SubtypeRelation (otype A) :=
| S_OType            : forall (ol or: bool) (lhs rhs: A), ol <= or -> [S] lhs <: rhs -> [S_otype S] Ot ol lhs <: Ot or rhs
.
Global Instance SOf_otype {A: Set} {S: SubtypeOf A} : SubtypeOf (otype A) := S_otype S.
Inductive S_vtype {A: Set} (S: SubtypeRelation A) : SubtypeRelation (vtype A) :=
| S_Void             : [S_vtype S] @VVoid A <: VVoid
| S_NotVoid          : forall (lhs rhs: A), [S] lhs <: rhs -> [S_vtype S] Vt lhs <: Vt rhs
.
Global Instance SOf_vtype {A: Set} {S: SubtypeOf A} : SubtypeOf (vtype A) := S_vtype S.
Inductive S_tparam {A: Set} (S: SubtypeRelation A) : SubtypeRelation (tparam A) :=
| S_TParam           : forall (vl vr: variance) (name: string) (supl supr: list A),
    [S_variance] vl <: vr -> [S_Intersect S] supl <: supr ->
    [S_tparam S] TParam vl name supl <: TParam vr name supr
.
Global Instance SOf_tparam {A: Set} {S: SubtypeOf A} : SubtypeOf (tparam A) := S_tparam S.
Inductive S_itype {A: Set} (S: SubtypeRelation A) : SubtypeRelation (itype A) :=
| S_Ident            : forall (name: string) (tal tar: list A), [S_Zip S] tal <: tar -> [S_itype S] It name tal <: It name tar
.
Global Instance SOf_itype {A: Set} {S: SubtypeOf A} : SubtypeOf (itype A) := S_itype S.
Inductive S_stype {A: Set} (S: SubtypeRelation A) : SubtypeRelation (stype A) :=
| S_Fn               : forall (tpl tpr: list (tparam A)) (thispl thispr: A)
                         (pl pr: list (otype A)) (rl rr: A) (retl retr: (vtype A)),
    [S_Zip (S_tparam S)] tpl :> tpr -> [S] thispl :> thispr -> [S_Zip (S_otype S)] pl :> pr -> [S] rl :> rr -> [S_vtype S] retl <: retr ->
    [S_stype S] SFn tpl thispl pl rl retl <: SFn tpr thispr pr rr retr
| S_Array            : forall (el er: A),                     [S]                     el <: er  -> [S_stype S] SArray el   <: SArray er
| S_Tuple            : forall (esl esr: list (otype A)),      [S_Zip (S_otype S)]    esl <: esr -> [S_stype S] STuple esl  <: STuple esr
| S_Object           : forall (fsl fsr: js_record (otype A)), [S_JsrZip (S_otype S)] fsl <: fsr -> [S_stype S] SObject fsl <: SObject fsr
.
Global Instance SOf_stype {A: Set} {S: SubtypeOf A} : SubtypeOf (stype A) := S_stype S.
Inductive S_ftype : SubtypeRelation ftype :=
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
.
Global Instance SOf_ftype : SubtypeOf ftype := S_ftype.
Axiom S_ftype_ind':
  forall (P: SubtypeRelation ftype)
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

Inductive HasVariance {A: Set} {S: SubtypeOf A} (lhs: A) (rhs: A): variance -> Prop :=
| IsBivariant     : lhs <: rhs \/ lhs :> rhs -> HasVariance lhs rhs Bivariant
| IsCovariant     : lhs <: rhs              -> HasVariance lhs rhs Covariant
| IsContravariant :              lhs :> rhs -> HasVariance lhs rhs Contravariant
| IsInvariant     : lhs <: rhs -> lhs :> rhs -> HasVariance lhs rhs Invariant
.

Definition IsBounded {A: Set} {S: SubtypeOf A} (x min max: A): Prop := min <: x /\ x <: max.
Notation "min '<:' x '<:' max" := (IsBounded x min max) (at level 64, no associativity).

Definition Union {A: Set} {S: SubtypeOf A} (lhs rhs uni: A): Prop := uni <: lhs /\ uni <: rhs /\ forall a, a <: lhs -> a <: rhs -> a <: uni.
Notation "'(U)'" := Union.
Notation "lhs 'U' rhs '=' a" := (Union lhs rhs a) (at level 60, rhs at next level, no associativity).

Definition Intersection {A: Set} {S: SubtypeOf A} (lhs rhs int: A): Prop := lhs <: int /\ rhs <: int /\ forall a, a <: int -> a <: lhs /\ a <: rhs.
Notation "'(I)'" := Intersection.
Notation "lhs 'I' rhs '=' a" := (Intersection lhs rhs a) (at level 60, rhs at next level, no associativity).

Local Ltac ind1 a :=
  lazymatch type of a with
  | js_record _ => induction a
  | list _ => induction a
  | _ => destruct a
  end.

Local Ltac ind2 a b :=
  lazymatch type of a with
  | js_record _ => induction2 a b using ind_list2
  | list _ => induction2 a b using ind_list2
  | _ => destruct a; destruct b
  end.

Local Ltac ind_s a b :=
  tryif constr_eq a b then ind1 a else ind2 a b.

Local Ltac inv_con3 a Inv :=
  ind1 a; try (inv Inv); try econstructor; simpl; try (reflexivity || discriminate).

Local Ltac inv_con_Intersect supers Inv :=
  ind1 supers; inv Inv; [constructor |];
  let a := fresh "a" in let supers := fresh "supers'" in
  match goal with
  | |- [_] (?a' :: ?supers') <: (?a' :: ?supers') => rename a' into a; rename supers' into supers
  end;
  unshelve econstructor; [exact a | exact supers | | | apply List.Add_head].

Local Ltac inv_con_JsrZip fields Inv :=
  ind1 fields; inv Inv; [constructor |];
  let a := fresh "a" in let fields := fresh "fields'" in
  match goal with
  | |- [_] (?a' :: ?fields') <: (?a' :: ?fields') => rename a' into a; rename fields' into fields
  end;
  destruct a as [kx vx]; simpl in *;
  unshelve econstructor; [exact vx | exact fields | | | apply JsRecordAdd_head].

Local Ltac inv_con2 S a :=
  let Inv := fresh "Inv" in
  match goal with
  | Inv' : ?P ?a' |- _ => constr_eq a a'; rename Inv' into Inv
  | _ => idtac
  end;
  lazymatch S with
  | S_JsrZip _ => inv_con_JsrZip a Inv
  | S_Intersect _ => inv_con_Intersect a Inv
  | _ => inv_con3 a Inv
  end.

Local Ltac is_var' a := first [is_var a | is_evar a].

Local Ltac inv_con1 S a :=
  tryif is_var' a then inv_con2 S a else fail "tried to inv_con non-variables".

Local Ltac inv_con0 S a :=
  lazymatch a with
  | ?P ?a => inv_con1 S a
  | ?a => inv_con1 S a
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
  | |- ?a >= ?a => destruct a; reflexivity
  | |- ?a <= ?a => destruct a; reflexivity
  | G : forall (a: ftype), a <: a |- ?a <: ?a => exact (G a) || fail "mismatched inductive end-case"
  | |- _ => idtac
  end.

(* Destruct or induct on goal, invert dependent hypotheses, apply the corresponding constructor *)
Local Ltac inv_con :=
  lazymatch goal with
  | |- [?S] ?a <: ?a => inv_con0 S a
  | |- _ => fail "not inv_con supported"
  end; post_inv_con.

Local Ltac inv_con' := repeat progress inv_con.

Theorem subtype_refl: forall (a: ftype), a <: a.
Proof with inv_con'.
  induction a using ftype_rec'; intros.
  - constructor.
  - destruct nullable; constructor; simpl; reflexivity.
  - constructor; [destruct nullable; simpl; reflexivity |]...
  - constructor; [destruct nullable; simpl; reflexivity | |]...
    (* Tactic has trouble because we have id :: sids instead of a single term *)
    unshelve econstructor; [exact id | exact sids | | | apply List.Add_head]; post_inv_con...
Qed.

Local Ltac destruct_conj :=
  lazymatch goal with
  | H : ?P /\ ?Q |- _ => destruct H
  end.

Local Ltac assert_to_solve' eqs :=
  assert eqs; [repeat split | repeat destruct_conj; subst; reflexivity].

Local Ltac assert_to_solve :=
  lazymatch goal with
  | |- ?P ?a ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 = ?P ?b ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 => assert_to_solve' (a = b /\ a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4 /\ a5 = b5)
  | |- ?P ?a ?a0 ?a1 ?a2 ?a3 ?a4 = ?P ?b ?b0 ?b1 ?b2 ?b3 ?b4 => assert_to_solve' (a = b /\ a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4)
  | |- ?P ?a ?a0 ?a1 ?a2 ?a3 = ?P ?b ?b0 ?b1 ?b2 ?b3 => assert_to_solve' (a = b /\ a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3)
  | |- ?P ?a ?a0 ?a1 ?a2 = ?P ?b ?b0 ?b1 ?b2 => assert_to_solve' (a = b /\ a0 = b0 /\ a1 = b1 /\ a2 = b2)
  | |- ?P ?a ?a0 ?a1 = ?P ?b ?b0 ?b1 => assert_to_solve' (a = b /\ a0 = b0 /\ a1 = b1)
  | |- ?P ?a ?a0 = ?P ?b ?b0 => assert_to_solve' (a = b /\ a0 = b0)
  | |- ?P ?a = ?P ?b => assert_to_solve' (a = b)
  | |- ?P = ?P => reflexivity
  | |- _ => idtac "can't assert_to_solve"
  end.

Local Ltac inv_eq2 H H0 S a b :=
  ind2 a b; inv H; inv H0; assert_to_solve.

Local Ltac inv_eq1 H H0 S a b :=
  is_var a; is_var b; inv_eq2 H H0 S a b.

Local Ltac inv_eq :=
  lazymatch goal with
  (* Special cases *)
  | H7 : [S_stype S_ftype] SFn nil ?thisp ?params ?rparam ?ret :> SFn (?y :: ?ys) ?thisp0 ?params0 ?rparam0 ?ret0 |- _ => inv H7
  | H9 : [S_Zip _] (?y :: ?ys) :> nil |- _ => inv H9
  | H22 : List.Add ?l ?ls ?nil |- _ => inv H22
  (* Cases *)
  | H : [?S] ?a :> ?b, H0 : [?S0] ?b :> ?a |- ?a = ?b => inv_eq1 H H0 S a b
  | |- _ => fail "can't inv_eq"
  end.

Local Ltac inv_eq' := repeat progress inv_eq.

Theorem subtype_antisym: forall (a b: ftype), a <: b -> b <: a -> a = b.
Proof with inv_eq'.
  intros a b H. induction H using S_ftype_ind'; intros.
  - inv H; reflexivity.
  - inv H; [reflexivity | inv H0].
  - inv H0; [inv H | reflexivity].
  - inv H1; assert_to_solve; [destruct nl; destruct nr; reflexivity || discriminate |].
    inv_eq. inv_eq. inv_eq. inv_eq. inv_eq. inv_eq. inv_eq. inv_eq. inv_eq.

    assert (nl = nr); [destruct nl; destruct nr; reflexivity || discriminate | subst].
    assert (sl = sr); [ind2 sl sr; inv H7 | subst; reflexivity].
    + assert (tparams = tparams0); [ind2 tparams tparams0; inv H9 | subst].
    ind2 sl sr; inv H7.
    lazymatch goal with
    destruct sl; destruct sr; inv H7.
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
