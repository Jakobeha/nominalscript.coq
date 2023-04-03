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
Require Import LibHyps.LibHyps.
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
| S_JsrZip_cons      : forall (k: string) (vl vr: A) (ls ls' rs: js_record A),
    [S] vl <: vr -> [S_JsrZip S] ls <: rs -> JsRecordAdd k vl ls ls' -> [S_JsrZip S] ls' <: ((k, vr) :: rs)
.
Inductive S_Intersect {A: Set} (S: SubtypeRelation A) : SubtypeRelation (list A) :=
| S_Intersect_nil    : forall (lhs: list A), [S_Intersect S] lhs <: nil
| S_Intersect_cons   : forall (l r: A) (ls rs: list A),
    [S] l <: r -> [S_Intersect S] ls <: rs -> [S_Intersect S] (l :: ls) <: (r :: rs)
| S_Intersect_cons_l : forall (l: A) (ls rs: list A),
                 [S_Intersect S] ls <: rs -> [S_Intersect S] (l :: ls) <: rs
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

Local Ltac ind3 a b c :=
  lazymatch type of a with
  | js_record _ => induction3 a b c using ind_list3
  | list _ => induction3 a b c using ind_list3
  | _ => destruct a; destruct b; destruct c
  end.

Local Ltac ind_s a b :=
  tryif constr_eq a b then ind1 a else ind2 a b.

Local Ltac inv_con3 a Inv :=
  ind1 a; try (inv Inv); try econstructor; simpl; try (reflexivity || discriminate).

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
  - constructor; [destruct nullable; simpl; reflexivity | |]; [constructor |]...
Qed.

Lemma S_Intersect_length: forall {A: Set} (S: SubtypeRelation A) (lhs rhs: list A),
    [S_Intersect S] lhs <: rhs -> (List.length rhs <= List.length lhs)%nat.
Proof.
  intros; induction H; simpl.
  - apply Nat.le_0_l.
  - apply -> Nat.succ_le_mono; exact IHS_Intersect.
  - apply Nat.le_le_succ_r; exact IHS_Intersect.
Qed.

Local Ltac destruct_conj :=
  lazymatch goal with
  | H : ?P /\ ?Q |- _ => destruct H
  end.

Local Ltac assert_to_solve' eqs :=
  assert eqs; [repeat split | repeat destruct_conj; subst; reflexivity].

Local Ltac assert_to_solve :=
  lazymatch goal with
  | |- (?a, ?a0) :: ?a1 = (?b, ?b0) :: ?b1 => assert_to_solve' (a = b /\ a0 = b0 /\ a1 = b1)
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

Local Ltac pre_inv_eq_Intersect supers supers0 :=
  assert (List.length supers = List.length supers0); [apply Nat.le_antisymm; eapply S_Intersect_length; match goal with | H : [S_Intersect _] ?a :> ?b |- [S_Intersect _] ?a :> ?b => exact H end |].

Local Ltac pre_inv_eq S a b :=
  lazymatch S with
  | S_Intersect ?S => pre_inv_eq_Intersect a b
  | _ => idtac
  end.

Local Ltac inv_eq2 H H0 S a b :=
  pre_inv_eq S a b; ind2 a b; inv H; inv H0; assert_to_solve.

Local Ltac inv_eq1 H H0 S a b :=
  is_var a; is_var b; inv_eq2 H H0 S a b.

Local Ltac inv_eq :=
  lazymatch goal with
  (* Special cases *)
  | H7 : [S_stype S_ftype] SFn nil ?thisp ?params ?rparam ?ret :> SFn (?y :: ?ys) ?thisp0 ?params0 ?rparam0 ?ret0 |- _ => inv H7
  | H9 : JsRecordAdd ?k ?vl ?ls nil |- _ => inv H9
  | H9 : [S_Zip _] (?y :: ?ys) :> nil |- _ => inv H9
  | H22 : List.Add ?l ?ls ?nil |- _ => inv H22
  | H2 : Datatypes.length (?x :: ?xs0) = Datatypes.length (?y :: ?ys0) |- Datatypes.length ?xs0 = Datatypes.length ?ys0 => simpl in H2; inv H2; reflexivity
  | H2 : Datatypes.length (?x :: ?xs0) = Datatypes.length (?y :: ?ys0),
    H11 : [S_Intersect _] (?y :: ?ys0) :> ?xs0 |- _ => apply S_Intersect_length in H11; simpl in H11; inv H11; simpl in H2; inv H2; lia
  | H2 : Datatypes.length (?x :: ?xs0) = Datatypes.length (?y :: ?ys0),
    H11 : [S_Intersect _] (?x :: ?xs0) :> ?ys0 |- _ => apply S_Intersect_length in H11; simpl in H11; inv H11; simpl in H2; inv H2; lia
  | H10 : ?optional >= ?optional0, H4 : ?optional0 >= ?optional |- ?optional = ?optional0 => destruct optional; destruct optional0; reflexivity || discriminate
  | IH : [fun a0 b0 : ftype => a0 :> b0 -> a0 = b0] ?a :> ?b |- ?b = ?a => apply IH; try assumption
  | IH : [fun a0 b0 : ftype => a0 :> b0 -> a0 = b0] ?a :> ?b |- ?a = ?b => symmetry; apply IH; try assumption
  | IH : ?Q -> ?P |- ?P => apply IH; try assumption
  | IH : ?Q -> ?Q0 -> ?P |- ?P => apply IH; try assumption
  | IH : ?Q -> ?Q0 -> ?Q1 -> ?P |- ?P => apply IH; try assumption
  | IH : ?Q -> ?Q0 -> ?Q1 -> ?Q2 -> ?P |- ?P => apply IH; try assumption
  | IH : ?Q -> ?Q0 -> ?Q1 -> ?Q2 -> ?Q3 -> ?P |- ?P => apply IH; try assumption
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
  - inv H1; assert_to_solve; [destruct nl; destruct nr; reflexivity || discriminate |]...
    (* TODO js_record case *)
    all: admit.
  - inv H1.
  - inv H2;
    assert (List.length (idl :: idsl) = List.length (idr :: idsr)); [ apply Nat.le_antisymm; eapply S_Intersect_length; [exact H12 | exact H0] | simpl in H2; inv H2];
    inv H12; [| apply S_Intersect_length in H7; simpl in H7; lia];
    inv H0; [| apply S_Intersect_length in H8; simpl in H8; lia].
    assert_to_solve; [destruct nl; destruct nr; reflexivity || discriminate | ..]...
    (* TODO js_record case *)
    all: admit.
Admitted.

Theorem subtype_Nullable: forall (a b: ftype), a <: b -> IsNullable a -> IsNullable b.
Proof.
  intros a b H. destruct H; intros; simpl in *;
    [reflexivity | contradiction | exact H | ..];
    destruct nl; destruct nr; reflexivity || contradiction || discriminate.
Qed.

Local Ltac inv_trans :=
    lazymatch goal with
    | H : ?nr >= ?nl |- ?nullable >= ?nl => destruct nullable; destruct nl; destruct nr; reflexivity || discriminate
    | |- [_] nil :> ?zs => constructor
    | IH : forall c0 a0, ?b :> c0 -> a0 :> ?b -> a0 :> c0, H : [S_ftype] ?b :> ?c, H0 : [S_ftype] ?a :> ?b |- [S_ftype] ?a :> ?c => apply IH; [exact H | exact H0]
    | IH : ?Q -> ?P |- ?P => apply IH; try assumption
    | IH : ?Q -> ?Q0 -> ?P |- ?P => apply IH; try assumption
    | IH : ?Q -> ?Q0 -> ?Q1 -> ?P |- ?P => apply IH; try assumption
    | IH : ?Q -> ?Q0 -> ?Q1 -> ?Q2 -> ?P |- ?P => apply IH; try assumption
    | IH : ?Q -> ?Q0 -> ?Q1 -> ?Q2 -> ?Q3 -> ?P |- ?P => apply IH; try assumption
    | IH : ?P ?b, H : [?S] ?a :> ?b, H0 : [?S0] ?b :> ?c |- context A [?a] => ind3 a b c; inv H; inv H0; inv IH; constructor
    | _ => fail "can't inv_trans"
    end.

Local Ltac inv_trans' := repeat progress inv_trans.

Theorem subtype_trans: forall (a b c: ftype), a <: b -> b <: c -> a <: c.
Proof with inv_trans'.
  intros a b; revert a; induction b using ftype_rec'; intros.
  - inv H0; constructor.
  - inv H; constructor; destruct nullable; simpl in H1; [clear H1 | contradiction]; inv H0; [simpl; reflexivity | exact H].
  - destruct a; destruct c; try apply S_Any; inv H0; inv H1; try (apply S_Never || apply S_Null); [destruct nullable; destruct nullable1; simpl in *; reflexivity || discriminate || contradiction | ..].
    inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans.
    inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. inv_trans. intros.
  - inv H; constructor.
  - inv H; constructor; inv H0.
  - inv H0; constructor; exact H.
  - destruct a; inv H1; try (apply S_Never || apply S_Null); [destruct nl; destruct nr; simpl in *; reflexivity || discriminate || contradiction | ..].
    inv_trans. inv_trans. inv_trans. inv_trans. unfold ap_SubtypeRelation in H14.
    apply H18.
    destruct nullable; destruct nl; destruct nr; try (reflexivity || discriminate).
    destruct structure; [inv H11 | inv H7 | inv H7 | inv H7 ].
Admitted.

Theorem union_never: forall (a: ftype), FNEVER U a = a.
Admitted.

Theorem union_null: forall (a: ftype), IsNullable a -> FNULL U a = a.
Admitted.

Theorem union_any: forall (a: ftype), FAny U a = FAny.
Admitted.

Theorem intersect_never: forall (a: ftype), FNEVER I a = FNEVER.
Admitted.

Theorem intersect_null: forall (a: ftype), IsNullable a -> FNULL I a = FNULL.
Admitted.

Theorem intersect_any: forall (a: ftype), FAny I a = a.
Admitted.

Theorem union_subtype: forall (a b ab c: ftype), a <: c -> b <: c -> a U b = ab -> ab <: c.
Admitted.

Theorem intersect_subtype: forall (a b ab c: ftype), c <: a -> c <: b -> a I b = ab -> c <: ab.
Admitted.

Theorem union_subtype0: forall (a b ab: ftype), a U b = ab -> a <: ab /\ b <: ab.
Admitted.

Theorem intersect_subtype0: forall (a b ab: ftype), a I b = ab -> ab <: a /\ ab <: b.
Admitted.

Theorem union_refl: forall (a: ftype), a U a = a.
Admitted.

Theorem intersect_refl: forall (a: ftype), a I a = a.
Admitted.

Theorem union_comm: forall (a b ab: ftype), a U b = ab <-> b U a = ab.
Admitted.

Theorem intersect_comm: forall (a b ab: ftype), a I b = ab <-> b I a = ab.
Admitted.

Theorem union_assoc: forall (a b c ab bc abc: ftype), a U b = ab -> b U c = bc -> ab U c = abc <-> a U bc = abc.
Admitted.

Theorem intersect_assoc: forall (a b c ab bc abc: ftype), a I b = ab -> b I c = bc -> ab I c = abc <-> a I bc = abc.
Admitted.

Theorem union_absorb: forall (a b ab: ftype), a <: b -> a U b = ab <-> a = ab.
Admitted.

Theorem intersect_absorb: forall (a b ab: ftype), a <: b -> a I b = ab <-> b = ab.
Admitted.
