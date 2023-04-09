(* Add LoadPath should not be necessary but it is *)
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Relations.Relation_Definitions.
From NS Require Import Misc.

Notation js_record A := (list (string * A)).

Fixpoint js_record_has_key {A: Type} (key: string) (a: js_record A): bool :=
match a with
| nil => false
| cons (x_key, _) xs => String.eqb key x_key || js_record_has_key key xs
end.

Fixpoint js_record_assoc {A: Type} (key: string) (a: js_record A): option A :=
match a with
| nil => None
| cons (x_key, x) xs => if String.eqb key x_key then Some x else js_record_assoc key xs
end.

Definition map_js_record {A B: Type} (f: A -> B) (a: js_record A): js_record B :=
  List.map (fun x => match x with (name, value) => (name, f value) end) a.

Fixpoint js_record_fields_superset {A B: Type} (a: js_record A) (b: js_record B): bool :=
match b with
| nil => true
| cons (b_key, _) bs => js_record_has_key b_key a && js_record_fields_superset a bs
end.

Definition js_record_fields_eqb {A B: Type} (a: js_record A) (b: js_record B): bool :=
  js_record_fields_superset a b && js_record_fields_superset b a.

Fixpoint js_record_zip_with {A B C: Type} (f: A -> B -> C) (a: js_record A) (b: js_record B): js_record C :=
match a with
| nil => nil
| cons (x_key, x) xs =>
    cons_opt (option_map ((fun z => (x_key, z)) << f x) (js_record_assoc x_key b)) (js_record_zip_with f xs b)
end.

Definition JsRecordForall {A: Type} (P: A -> Prop) : js_record A -> Prop := List.Forall (P << snd).

Definition JsRecordHasKey {A: Type} (key: string): js_record A -> Prop :=
  List.Exists (fun '(key', _) => key = key').

Definition JsRecordSuperKeys {A: Type} (xs ys: js_record A): Prop :=
  forall k, JsRecordHasKey k xs -> JsRecordHasKey k ys.

Definition JsRecordEqKeys {A: Type} (xs ys: js_record A): Prop :=
  forall k, JsRecordHasKey k xs <-> JsRecordHasKey k ys.

Inductive JsRecordEqKeys0 {A: Type}: js_record A -> js_record A -> Prop :=
| JsRecordEqKeys0_nil : JsRecordEqKeys0 nil nil
| JsRecordEqKeys0_add : forall (k: string) (vx vy: A) (xs ys xs' ys': js_record A), JsRecordEqKeys0 xs ys -> List.Add (k, vx) xs xs' -> List.Add (k, vy) ys ys' -> JsRecordEqKeys0 xs' ys'
.

Inductive JsRecordAdd {A: Type} (kx: string) (vx: A) : js_record A -> js_record A -> Prop :=
| JsRecordAdd_head : forall (xs: js_record A), ~JsRecordHasKey kx xs -> JsRecordAdd kx vx xs ((kx, vx) :: xs)%list
| JsRecordAdd_cons : forall (kx0: string) (vx0: A) (xs xs': js_record A), kx0 <> kx -> JsRecordAdd kx vx xs xs' -> JsRecordAdd kx vx ((kx0, vx0) :: xs)%list ((kx0, vx0) :: xs')%list
.

Inductive JsRecordNoDup {A: Type} : js_record A -> Prop :=
| JsRecordNoDup_nil : JsRecordNoDup nil
| JsRecordNoDup_cons : forall kx vx xs, JsRecordNoDup xs -> not (JsRecordHasKey kx xs) -> JsRecordNoDup ((kx, vx) :: xs)%list
.

Inductive JsRecordNoDupForall {A: Type} (P: A -> Prop): js_record A -> Prop :=
| JsRecordNoDupForall_nil : JsRecordNoDupForall P nil
| JsRecordNoDupForall_cons : forall kx vx xs, JsRecordNoDupForall P xs -> ~ JsRecordHasKey kx xs -> P vx -> JsRecordNoDupForall P ((kx, vx) :: xs)%list
.

(** 2-way relation: same keys and values are related *)
Inductive JsRecordRel {A: Type} (rel: relation A): relation (js_record A) :=
| JsRecordRel_nil : JsRecordRel rel nil nil
| JsRecordRel_cons : forall (k: string) (vx vy: A) (xs xs' ys: js_record A),
    rel vx vy -> JsRecordRel rel xs ys -> JsRecordAdd k vx xs xs' -> ~ JsRecordHasKey k ys -> JsRecordRel rel xs' ((k, vy) :: ys)%list
.

(** 1-way relation: lhs may have extra keys with unrelated values *)
Inductive JsRecord1Rel {A: Set} (rel: relation A): relation (js_record A) :=
| JsRecord1Rel_nil       : forall (lhs: js_record A), JsRecordNoDup lhs -> JsRecord1Rel rel lhs nil
| JsRecord1Rel_cons      : forall (k: string) (vl vr: A) (ls rs rs': js_record A),
   rel vl vr -> JsRecord1Rel rel ls rs -> JsRecordAdd k vr rs rs' -> ~JsRecordHasKey k ls -> JsRecord1Rel rel ((k, vl) :: ls)%list rs'
| JsRecord1Rel_cons_l    : forall (k: string) (vl: A) (ls rs: js_record A),
               JsRecord1Rel rel ls rs -> ~JsRecordHasKey k rs    -> ~JsRecordHasKey k ls -> JsRecord1Rel rel ((k, vl) :: ls)%list rs
.

Ltac rewrite_Forall_Exists_neg A key :=
  let H := fresh "H" in
  replace (fun '(key', _) => key <> key') with (fun (x: string * A) => not ((fun '(key', _) => key = key') x)) in *;
  try (apply functional_extensionality; intros H; destruct H; reflexivity);
  rewrite List.Forall_Exists_neg in *.

Theorem JsRecordHasKey_dec: forall {A: Type} (key: string) (xs: js_record A),
    JsRecordHasKey key xs \/ not (JsRecordHasKey key xs).
Proof.
  intros; induction xs.
  - right; intros H; inversion H.
  - destruct a; destruct (string_dec key s).
    + left; subst; apply List.Exists_cons_hd; reflexivity.
    + destruct IHxs; [left | right].
      * apply List.Exists_cons_tl; exact H.
      * intros H0; inversion H0; subst.
        --  contradiction (n eq_refl).
        --  contradiction (H H2).
Qed.

Theorem JsRecordHasKey_neg: forall {A: Type} (key: string) (xs: js_record A),
    not (JsRecordHasKey key xs) <-> List.Forall (fun '(key', _) => key <> key') xs.
Proof.
  split; intros; rewrite_Forall_Exists_neg A key; exact H.
Qed.

Theorem JsRecordHasKey_alt: forall {A: Type} (key: string) (xs: js_record A),
    JsRecordHasKey key xs <-> not (List.Forall (fun '(key', _) => key <> key') xs).
Proof.
  split; intros; rewrite_Forall_Exists_neg A key.
  - intros H0; contradiction (H0 H).
  - apply Decidable.not_not; unfold Decidable.decidable; [apply JsRecordHasKey_dec | exact H].
Qed.

Theorem JsRecordHasKey_neg_Add : forall {A: Type} (kx' : string) (xs': js_record A),
  not (JsRecordHasKey kx' xs') ->
  forall (kx: string) (vx: A) (xs: js_record A),
  List.Add (kx, vx) xs xs' ->
  kx' <> kx /\ not (JsRecordHasKey kx' xs).
Proof.
  intros A kx' xs'; induction xs'; intros; inv H0; rewrite JsRecordHasKey_neg in *; inv H.
  - split; assumption.
  - destruct a; subst; rename s into kx0; split.
    + intros H; subst. rewrite List.Forall_forall in H4; pose (H := List.Add_in H3); pose (H0 := List.in_eq (kx, vx) l); rewrite <- H in H0; specialize (H4 _ H0); simpl in H4; contradiction (H4 eq_refl).
    + apply List.Forall_cons; [exact H2 |]. rewrite <- JsRecordHasKey_neg; eapply proj2; eapply (IHxs' H4); exact H3.
Qed.

Corollary JsRecordHasKey_neg_Add0 : forall {A: Type} (kx' : string) (xs': js_record A),
  not (JsRecordHasKey kx' xs') ->
  forall (kx: string) (vx: A) (xs: js_record A),
  List.Add (kx, vx) xs xs' ->
  not (JsRecordHasKey kx' xs).
Proof.
  intros; eapply proj2; eapply JsRecordHasKey_neg_Add; [exact H | exact H0].
Qed.

Theorem JsRecordHasKey_In: forall {A: Type} (key: string) (xs: js_record A),
    JsRecordHasKey key xs <-> exists x, List.In (key, x) xs.
Proof.
  split; intros.
  - induction H.
    + destruct x as [kx vx]; subst; exists vx; simpl; left; reflexivity.
    + destruct IHExists as [vx IHExists]; exists vx; simpl; right; exact IHExists.
  - destruct H as [vx H]; destruct xs; [inv H |]; destruct p as [kx0 vx0]; simpl in H; destruct H.
    + inv H; constructor; reflexivity.
    + apply List.Exists_cons_tl; rewrite List.Exists_exists; exists (key, vx); split; [exact H | reflexivity].
Qed.

Theorem JsRecordHasKey_In0: forall {A: Type} (key: string) (x: A) (xs: js_record A),
    List.In (key, x) xs -> JsRecordHasKey key xs.
Proof.
  intros; rewrite JsRecordHasKey_In; exists x; exact H.
Qed.

Theorem JsRecordHasKey_In_cons: forall {A: Type} (k: string) (vx vx0: A) (xs: js_record A),
    List.In (k, vx) ((k, vx0) :: xs) ->
    ~ JsRecordHasKey k xs ->
    vx = vx0.
Proof.
  intros; inv H; [inv H1; reflexivity |]; rewrite JsRecordHasKey_In in H0; contradict H0; exists vx; exact H1.
Qed.

Theorem JsRecordHasKey_uncons: forall {A: Type} (k k0: string) (vx: A) (xs: js_record A),
    JsRecordHasKey k ((k0, vx) :: xs) -> k = k0 \/ JsRecordHasKey k xs.
Proof.
  destruct xs; intros; destruct (string_dec k k0); (subst; left; reflexivity) || right.
  - inv H; [contradiction | inv H1].
  - destruct p as [kx1 vx1]; inv H; [contradiction | assumption].
Qed.

Theorem JsRecordHasKey_uncons0: forall {A: Type} (k k0: string) (vx: A) (xs: js_record A),
    JsRecordHasKey k ((k0, vx) :: xs) -> ~JsRecordHasKey k xs -> k = k0.
Proof.
  intros; apply JsRecordHasKey_uncons in H; destruct H; [exact H | contradiction].
Qed.

Theorem JsRecordHasKey_uncons1: forall {A: Type} (k k0: string) (vx: A) (xs: js_record A),
    JsRecordHasKey k ((k0, vx) :: xs) -> k <> k0 -> JsRecordHasKey k xs.
Proof.
  intros; apply JsRecordHasKey_uncons in H; destruct H; [contradiction | exact H].
Qed.

Theorem JsRecordNoDup_add0 : forall {A: Type} (xs': js_record A) (kx: string) (vx: A) (xs: js_record A),
  JsRecordNoDup xs' ->
  List.Add (kx, vx) xs xs' ->
  JsRecordNoDup xs.
Proof.
  intros A xs'; induction xs'; intros; inv H0; inv H; [exact H2 |]; apply JsRecordNoDup_cons.
  - apply (IHxs' kx vx l); assumption.
  - eapply (JsRecordHasKey_neg_Add0 H4); exact H3.
Qed.

Theorem JsRecordNoDup_add1 : forall {A: Type} (xs': js_record A) (kx: string) (vx: A) (xs: js_record A),
  JsRecordNoDup xs' ->
  List.Add (kx, vx) xs xs' ->
  not (JsRecordHasKey kx xs).
Proof.
  intros A xs'; induction xs'; intros; inv H0; inv H; [exact H4 |]; rewrite JsRecordHasKey_neg; apply List.Forall_cons.
  - intros H; subst; rewrite JsRecordHasKey_neg, List.Forall_forall in H4; pose (H := List.Add_in H3); pose (H0 := List.in_eq (kx0, vx) l); rewrite <- H in H0; specialize (H4 _ H0); simpl in H4; contradiction (H4 eq_refl).
  - rewrite <- JsRecordHasKey_neg. eapply IHxs'; [exact H2 | exact H3].
Qed.

Theorem JsRecordNoDup_add : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
  JsRecordNoDup xs' ->
  List.Add (kx, vx) xs xs' ->
  JsRecordNoDup xs /\ not (JsRecordHasKey kx xs).
Proof.
  split; [eapply JsRecordNoDup_add0 | eapply JsRecordNoDup_add1]; [exact H | exact H0 | exact H | exact H0].
Qed.


Theorem JsRecordNoDupForall_alt : forall {A: Type} (P: A -> Prop) (xs: js_record A),
    JsRecordNoDupForall P xs <-> JsRecordNoDup xs /\ JsRecordForall P xs.
Proof.
  split; intros.
  - induction H; split; constructor; destruct IHJsRecordNoDupForall; simpl; assumption.
  - induction xs; [| destruct a as [kx vx]]; constructor.
    + apply IHxs; split_with H; inv H; assumption.
    + apply proj1 in H; inv H; exact H4.
    + apply proj2 in H; inv H; simpl in H2; exact H2.
Qed.

Theorem JsRecordAdd_not_nil : forall {A: Type} (kx: string) (vx: A) (xs: js_record A),
    not (JsRecordAdd kx vx xs nil).
Proof.
  intros; intros H; inv H.
Qed.

Theorem JsRecordAdd_HasKey : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> JsRecordHasKey kx xs'.
Proof.
  intros; induction H; [apply List.Exists_cons_hd; reflexivity | apply List.Exists_cons_tl; exact IHJsRecordAdd].
Qed.

Theorem JsRecordAdd_HasKey0 : forall {A: Type} (kx kx0: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> JsRecordHasKey kx0 xs -> JsRecordHasKey kx0 xs'.
Proof.
  intros; induction H; [apply List.Exists_cons_tl; exact H0 |]; destruct (string_dec kx0 kx1).
  - subst; apply List.Exists_cons_hd; reflexivity.
  - inv H0; [contradiction n; reflexivity |]; apply List.Exists_cons_tl; apply IHJsRecordAdd; exact H3.
Qed.

Theorem JsRecordAdd_HasKey1 : forall {A: Type} (kx kx0: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> JsRecordHasKey kx0 xs' -> kx <> kx0 -> JsRecordHasKey kx0 xs.
Proof.
  intros; induction H; [inv H0; [contradiction | exact H3] |]; destruct (string_dec kx0 kx1).
  - subst; apply List.Exists_cons_hd; reflexivity.
  - inv H0; [contradiction n; reflexivity |]; apply List.Exists_cons_tl; apply IHJsRecordAdd; exact H4.
Qed.

Theorem JsRecordAdd_not_HasKey : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> ~ JsRecordHasKey kx xs.
Proof.
  intros; induction H; [exact H |]; intros n; inv n; [contradiction H; reflexivity |]; contradiction IHJsRecordAdd.
Qed.

Theorem JsRecordAdd_not_HasKey0 : forall {A: Type} (kx kx0: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> ~ JsRecordHasKey kx0 xs' -> ~ JsRecordHasKey kx0 xs.
Proof.
  intros; induction H; intros n; [contradict H0; apply List.Exists_cons_tl; exact n |].
  inv n; [contradict H0; apply List.Exists_cons_hd; reflexivity |].
  contradict H3; apply IHJsRecordAdd; intros n; contradict H0; apply List.Exists_cons_tl; exact n.
Qed.

Theorem JsRecordAdd_not_HasKey1 : forall {A: Type} (kx kx0: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> ~ JsRecordHasKey kx0 xs -> kx <> kx0 -> ~ JsRecordHasKey kx0 xs'.
Proof.
  intros; induction H; intros n; [inv n; [contradiction H1; reflexivity | contradiction (H0 H3)] |].
  inv n; [contradict H0; apply List.Exists_cons_hd; reflexivity |].
  revert H4; apply IHJsRecordAdd; intros H4; contradict H0; apply List.Exists_cons_tl; exact H4.
Qed.

Theorem JsRecordAdd_from_HasKey : forall {A: Type} (kx: string) (xs': js_record A),
    JsRecordNoDup xs' -> JsRecordHasKey kx xs' -> exists vx xs, JsRecordAdd kx vx xs xs'.
Proof.
  induction xs'; intros; inv H H0.
  - exists vx; exists xs'; apply JsRecordAdd_head; assumption.
  - specialize (IHxs' H3 H1); destruct IHxs' as [vx0 [xs IHxs']]; exists vx0; exists ((kx0, vx) :: xs)%list; apply JsRecordAdd_cons; [| assumption]; intros n; subst; contradict H4; exact H1.
Qed.

Theorem JsRecordAdd_ListAdd : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> List.Add (kx, vx) xs xs'.
Proof.
  intros. induction H; constructor. exact IHJsRecordAdd.
Qed.

Theorem JsRecordAdd_Forall : forall {A: Type} (P: A -> Prop) (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> JsRecordForall P xs' -> P vx /\ JsRecordForall P xs.
Proof.
  intros. apply JsRecordAdd_ListAdd in H. unfold JsRecordForall in *. rewrite List.Forall_forall in *. split.
  - specialize (H0 (kx, vx)). simpl in H0. apply H0. rewrite (List.Add_in H). simpl. left. reflexivity.
  - intros. specialize (H0 x). destruct x as [kx0 vx0]. simpl in *. apply H0. rewrite (List.Add_in H). simpl. right. exact H1.
Qed.

Theorem JsRecordAdd_In : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> List.In (kx, vx) xs'.
Proof.
  intros; induction H; [left; reflexivity | right; exact IHJsRecordAdd].
Qed.

Theorem JsRecordAdd_not_In : forall {A: Type} (kx: string) (vx vx0: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> ~List.In (kx, vx0) xs.
Proof.
  intros; induction H; intros n; [contradict H; apply JsRecordHasKey_In0 with vx0; exact n |].
  contradict IHJsRecordAdd; inv n; [| exact H1]; inv H1; contradict H; reflexivity.
Qed.

Theorem JsRecordAdd_In0 : forall {A: Type} (kx kx0: string) (vx vx0: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> List.In (kx0, vx0) xs -> kx0 <> kx /\ List.In (kx0, vx0) xs'.
Proof.
  intros; induction H; [destruct (string_dec kx0 kx); [subst; contradict H; apply JsRecordHasKey_In0 with vx0; exact H0 | split; [exact n | right; exact H0]] |]; split.
  - destruct (string_dec kx0 kx); [| exact n]; subst; eapply proj1; apply IHJsRecordAdd; inv H0; [inv H2; contradiction H; reflexivity | exact H2].
  - inv H0; [inv H2; left; reflexivity | right; eapply proj2; apply IHJsRecordAdd; exact H2].
Qed.

Theorem JsRecordAdd_from_In : forall {A: Type} (kx: string) (vx: A) (xs': js_record A),
    JsRecordNoDup xs' -> List.In (kx, vx) xs' -> exists xs, JsRecordAdd kx vx xs xs'.
Proof.
  induction xs'; intros; inv H H0.
  - inv H; exists xs'; apply JsRecordAdd_head; assumption.
  - specialize (IHxs' H3 H); destruct IHxs' as [xs IHxs']; exists ((kx0, vx0) :: xs)%list; apply JsRecordAdd_cons; [| assumption]; intros n; subst; contradict H4; apply JsRecordHasKey_In0 with vx; assumption.
Qed.

Theorem JsRecordAdd_is_cons : forall {A: Type} (kx: string) (vx vx': A) (xs xs': js_record A),
    JsRecordAdd kx vx xs ((kx, vx') :: xs')%list -> vx = vx' /\ xs = xs'.
Proof.
  intros; inv H; [split; reflexivity | contradiction H3; reflexivity].
Qed.

Theorem JsRecordAdd_no_refl : forall {A: Type} (kx: string) (vx: A) (xs: js_record A),
    ~ (JsRecordAdd kx vx xs xs).
Proof.
  intros; intros H; apply JsRecordAdd_ListAdd, List.Add_length in H; remember (Datatypes.length xs) as n; clear Heqn.
  (* This should be automatic or trivial... *)
  induction n; [discriminate H |]; inv H; exact (IHn H1).
Qed.

Theorem JsRecordAdd_no_head : forall {A: Type} (kx: string) (vx: A) (xs xs0: js_record A),
    ~ (JsRecordAdd kx vx (xs0 ++ xs)%list xs).
Proof.
  intros; intros H; apply JsRecordAdd_ListAdd, List.Add_length in H; rewrite List.app_length in H;
    remember (Datatypes.length xs) as n; remember (Datatypes.length xs0) as m; clear Heqn Heqm.
  contradiction (Nat.succ_add_discr m n).
Qed.

Theorem JsRecordAdd_no_tail : forall {A: Type} (kx: string) (vx: A) (xs xs0: js_record A),
    ~ (JsRecordAdd kx vx (xs ++ xs0)%list xs).
Proof.
  intros; intros H; apply JsRecordAdd_ListAdd, List.Add_length in H; rewrite List.app_length in H;
    remember (Datatypes.length xs) as n; remember (Datatypes.length xs0) as m; clear Heqn Heqm; rewrite Nat.add_comm in H.
  contradiction (Nat.succ_add_discr m n).
Qed.

Theorem JsRecordAdd_cons_hd : forall {A: Type} (kx kx': string) (vx vx': A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> JsRecordAdd kx vx ((kx', vx') :: xs) ((kx', vx') :: xs') \/ kx = kx'.
Proof.
  intros; destruct (string_dec kx kx'); [right; exact e | left; apply JsRecordAdd_cons; [intros n'; symmetry in n'; contradiction (n n') | exact H]].
Qed.

Theorem JsRecordAdd_List_Forall : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> List.Forall (fun '(kx0, vx0) => vx = vx0 \/ kx0 <> kx) xs'.
Proof.
  intros; induction H; [| apply List.Forall_cons; [right; exact H | exact IHJsRecordAdd]].
  apply List.Forall_cons; [left; reflexivity |]; rewrite JsRecordHasKey_neg in H; eapply List.Forall_impl; [| exact H]; intros; destruct a as [kx0 vx0]; right; intros n; symmetry in n; contradiction (H0 n).
Qed.

Theorem JsRecordAdd_In_once : forall {A: Type} (kx: string) (vx vx0: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> List.In (kx, vx0) xs' -> vx = vx0.
Proof.
  intros. pose (JsRecordAdd_List_Forall H); rewrite List.Forall_forall in f; specialize (f _ H0); simpl in f; destruct f; [exact H1 | contradiction H1; reflexivity].
Qed.

Theorem JsRecordAdd_In_once' : forall {A: Type} (kx kx0: string) (vx vx0: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> List.In (kx0, vx0) xs' -> kx <> kx0 <-> List.In (kx0, vx0) xs.
Proof.
  split; intros.
  - induction H; simpl in H0; destruct H0; [inv H0; contradiction H1; reflexivity | exact H0 | inv H0; simpl; left; reflexivity | simpl; right; exact (IHJsRecordAdd H0)].
  - destruct (string_dec kx kx0); [subst; exfalso | exact n]; rewrite (JsRecordAdd_In_once _ H H0) in H; apply JsRecordAdd_not_HasKey, JsRecordHasKey_neg in H; rewrite List.Forall_forall in H; specialize (H _ H1); simpl in H; contradiction H; reflexivity.
Qed.

Theorem JsRecordAdd_join_key: forall {A: Type} (kx: string) (vx vx0: A) (xs xs0 xs': js_record A),
    JsRecordAdd kx vx xs xs' ->
    JsRecordAdd kx vx0 xs0 xs' ->
    vx = vx0.
Proof.
  intros; apply JsRecordAdd_In in H0; eapply JsRecordAdd_In_once in H; [exact H | exact H0].
Qed.
Ltac join_key_JsRecordAdd H H0 := remember (JsRecordAdd_join_key H H0) eqn:x; clear x; subst.

Theorem JsRecordAdd_NoDup_rev : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
  JsRecordNoDup xs' ->
  JsRecordAdd kx vx xs xs' ->
  ~JsRecordHasKey kx xs /\ JsRecordNoDup xs.
Proof.
  induction 2; split.
  - assumption.
  - inv H; assumption.
  - intros n; inv n; [contradiction |]; contradict H3; eapply proj1; apply IHJsRecordAdd; inv H; assumption.
  - inv H; apply JsRecordNoDup_cons; [eapply proj2; apply IHJsRecordAdd; assumption |]; apply JsRecordAdd_not_HasKey0 with kx vx xs'; assumption.
Qed.

Theorem JsRecordAdd_NoDup : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
  JsRecordNoDup xs ->
  JsRecordAdd kx vx xs xs' ->
  JsRecordNoDup xs'.
Proof.
  induction 2; constructor.
  - exact H.
  - exact H0.
  - apply IHJsRecordAdd; inv H; exact H4.
  - inv H; apply JsRecordAdd_not_HasKey1 with kx vx xs; [exact H1 | exact H6 | intros n'; symmetry in n'; contradiction (H0 n')].
Qed.

Theorem JsRecordRel_NoDup : forall {A: Type} {rel: relation A} (xs ys: js_record A),
    JsRecordRel rel xs ys -> JsRecordNoDup xs /\ JsRecordNoDup ys.
Proof.
  induction 1; [split; constructor |]; split_with IHJsRecordRel.
  - apply JsRecordAdd_NoDup with k vx xs; assumption.
  - apply JsRecordNoDup_cons; assumption.
Qed.

Lemma JsRecord1Rel_NoDup: forall {A: Set} {rel: relation A} (xs ys: js_record A),
    JsRecord1Rel rel xs ys -> JsRecordNoDup xs /\ JsRecordNoDup ys.
Proof.
  induction 1; [| destruct IHJsRecord1Rel ..]; split;
    [| constructor | constructor | apply JsRecordAdd_NoDup with k vr rs | constructor |]; assumption.
Qed.

Theorem JsRecordRel_HasKey: forall {A: Set} {rel: relation A} (xs ys: js_record A),
    JsRecordRel rel xs ys -> forall (k: string), JsRecordHasKey k xs <-> JsRecordHasKey k ys.
Proof.
  split; intros; induction H; [inv H0 | | inv H0 |]; destruct (string_dec k0 k).
  - subst; apply List.Exists_cons_hd; reflexivity.
  - apply List.Exists_cons_tl; apply IHJsRecordRel; apply JsRecordAdd_HasKey1 with k0 vx xs'; assumption.
  - subst; apply JsRecordAdd_HasKey with vx xs; assumption.
  - apply JsRecordAdd_HasKey0 with k0 vx xs; [assumption |]; apply IHJsRecordRel; inv H0; [contradiction | assumption].
Qed.

Lemma JsRecord1Rel_HasKey: forall {A: Set} {rel: relation A} (k: string) (xs ys: js_record A),
    JsRecord1Rel rel xs ys -> JsRecordHasKey k ys -> JsRecordHasKey k xs.
Proof.
  induction 1; intros; [inv H0 | |]; destruct (string_dec k k0); subst.
  - apply List.Exists_cons_hd; reflexivity.
  - apply List.Exists_cons_tl; apply IHJsRecord1Rel; apply JsRecordAdd_HasKey1 with k0 vr rs'; [exact H1 | exact H3 | intros n'; symmetry in n'; contradiction (n n')].
  - apply List.Exists_cons_hd; reflexivity.
  - apply List.Exists_cons_tl; apply IHJsRecord1Rel; exact H2.
Qed.

Lemma JsRecord1Rel_HasKey_neg: forall {A: Set} {rel: relation A} (k: string) (xs ys: js_record A),
    JsRecord1Rel rel xs ys -> ~JsRecordHasKey k xs -> ~JsRecordHasKey k ys.
Proof.
  intros; intros n; contradict H0; apply (@JsRecord1Rel_HasKey A rel) with ys; assumption.
Qed.


Theorem JsRecordRel_refl : forall {A: Type} {rel: relation A} (refl: reflexive A rel) (xs: js_record A),
    JsRecordNoDup xs -> JsRecordRel rel xs xs.
Proof.
  intros; induction xs; [| destruct a as [kx vx]]; econstructor; inv H; [apply refl | apply IHxs | apply JsRecordAdd_head |]; assumption.
Qed.

Theorem JsRecordAdd_join_orig: forall {A: Type} (kx: string) (vx vx0: A) (xs xs0 xs': js_record A),
    JsRecordNoDup xs' ->
    JsRecordAdd kx vx xs xs' ->
    JsRecordAdd kx vx0 xs0 xs' ->
    JsRecordRel eq xs xs0.
Proof.
  intros; revert H H0 H1; revert xs'; (induction2 xs0 xs using ind_list2); [constructor | inv H1 H2; contradiction | inv H1 H2; contradiction |].
  destruct x as [kx1 vx1], y as [ky1 vy1]; inv H0 H1 H2; try contradiction; [apply JsRecordRel_refl; [intros x; reflexivity | exact H3] |].
  econstructor; [reflexivity | apply H with xs0 | apply JsRecordAdd_head |]; try assumption; eapply JsRecordAdd_not_HasKey0; [exact H11 | exact H4 | exact H12 | exact H4].
Qed.

Theorem JsRecordRel_In_rev: forall {A: Set} {rel: relation A} (k: string) (vx vy: A) (xs ys: js_record A),
    JsRecordRel rel xs ys -> List.In (k, vx) xs -> List.In (k, vy) ys -> rel vx vy.
Proof.
  intros; induction H; [inv H1 |]; inv H3; destruct (string_dec k0 k); subst.
  - apply JsRecordHasKey_In_cons in H1; [| exact H4]; apply JsRecordHasKey_In_cons in H0; [| exact H5]; subst; exact H.
  - inv H0 H1; try (inv H3 + inv H0; contradiction n; reflexivity); exact (IHJsRecordRel H3 H0).
  - apply JsRecordHasKey_In_cons in H1; [| exact H4]; inv H0; [inv H3; contradiction H5; reflexivity |]; rewrite (JsRecordAdd_In_once _ H6 H3) in *; exact H.
  - inv H0 H1; try (inv H3 + inv H0; contradiction n; reflexivity).
    + inv H3; apply IHJsRecordRel; [simpl; left; reflexivity | exact H0].
    + pose (JsRecordAdd_In_once' _ _ H6 H3); apply i in n; apply IHJsRecordRel; [simpl; right; exact n | exact H0].
Qed.

Lemma JsRecord1Rel_In_rev: forall {A: Set} {rel: relation A} (k: string) (vx vy: A) (xs ys: js_record A),
    JsRecord1Rel rel xs ys -> List.In (k, vx) xs -> List.In (k, vy) ys -> rel vx vy.
Proof.
  intros; induction H; [inv H1 | | shelve]; inv H3; destruct (string_dec k0 k); subst.
  - apply JsRecordHasKey_In_cons in H1; [| exact H5]; apply JsRecordHasKey_In_cons in H0; [| exact H4]; subst. exact H.
  - inv H0 H1; try (inv H3 + inv H0; contradiction n; reflexivity); exact (IHJsRecord1Rel H3 H0).
  - apply JsRecordHasKey_In_cons in H0; [| exact H4]; inv H1; [inv H3; contradiction H5; reflexivity |]; rewrite (JsRecordAdd_In_once _ H6 H3) in *; exact H.
  - inv H0 H1; try (inv H3 + inv H0; contradiction n; reflexivity).
    + inv H0; apply IHJsRecord1Rel; [exact H3 | simpl; left; reflexivity].
    + pose (JsRecordAdd_In_once' _ _ H6 H0); apply i in n; apply IHJsRecord1Rel; [exact H3 | simpl; right; exact n].
Unshelve.
  inv H0.
  * inv H4; contradict H3; apply (@JsRecord1Rel_HasKey A rel) with rs; [exact H |]; apply JsRecordHasKey_In0 with vy; assumption.
  * apply IHJsRecord1Rel; assumption.
Qed.

Lemma JsRecord1Rel_add_rev: forall {A: Set} {rel: relation A} (k: string) (vx vy: A) (xs xs' ys ys': js_record A),
    JsRecordAdd k vx xs xs' -> JsRecordAdd k vy ys ys' -> JsRecord1Rel rel xs' ys' -> rel vx vy.
Proof.
  intros. apply JsRecordAdd_In in H, H0; eapply JsRecord1Rel_In_rev in H1; [exact H1 | exact H | exact H0].
Qed.

Theorem JsRecordRel_add_rev: forall {A: Set} {rel: relation A} (k: string) (vx vy: A) (xs xs' ys ys': js_record A),
    JsRecordAdd k vx xs xs' -> JsRecordAdd k vy ys ys' -> JsRecordRel rel xs' ys' -> rel vx vy.
Proof.
  intros. apply JsRecordAdd_In in H, H0; eapply JsRecordRel_In_rev in H1; [exact H1 | exact H | exact H0].
Qed.

Theorem JsRecordRel_In: forall {A: Set} {rel: relation A} (xs ys: js_record A),
    JsRecordRel rel xs ys -> forall (k: string) (vx vy: A), List.In (k, vx) xs -> List.In (k, vy) ys -> rel vx vy.
Proof.
  intros until ys; revert xs; induction ys; intros; [inv H1 |]; destruct a as [ky0 vy0]; inv H1.
  - inv H H2; rewrite (JsRecordAdd_In_once _ H8 H0) in *; exact H5.
  - destruct (string_dec ky0 k); [subst; apply JsRecordRel_NoDup, proj2 in H; inv H; contradict H6; apply JsRecordHasKey_In0 with vy; assumption |].
    inv H; apply IHys with xs0 k; try assumption; apply JsRecordAdd_In_once' with ky0 vx0 xs; assumption.
Qed.

Lemma JsRecord1Rel_In: forall {A: Set} {rel: relation A} (xs ys: js_record A),
    JsRecord1Rel rel xs ys -> forall (k: string) (vx vy: A), List.In (k, vx) xs -> List.In (k, vy) ys -> rel vx vy.
Proof.
  induction xs; intros; [inv H0 |]; destruct a as [kx0 vx0]; inv H0.
  - inv H H2; [inv H1 | rewrite (JsRecordAdd_In_once _ H8 H1) in *; exact H5 | ]; contradict H8; apply (@JsRecord1Rel_HasKey A rel) with ys; [exact H5 |]; apply JsRecordHasKey_In0 with vy; exact H1.
  - destruct (string_dec kx0 k); [subst; inv H; [inv H1 | contradict H9 | contradict H8]; apply JsRecordHasKey_In0 with vx; exact H2 |].
    inv H; [inv H1 | apply IHxs with rs k; try assumption; apply JsRecordAdd_In_once' with kx0 vr ys; assumption | apply IHxs with ys k; assumption].
Qed.

Theorem JsRecordRel_In0: forall {A: Set} {rel: relation A} (xs ys: js_record A),
    JsRecordNoDup xs -> JsRecordNoDup ys -> (forall k, JsRecordHasKey k xs <-> JsRecordHasKey k ys) ->
    (forall (k: string) (vx vy: A), List.In (k, vx) xs -> List.In (k, vy) ys -> rel vx vy) ->
    JsRecordRel rel xs ys.
Proof.
  intros until ys; revert xs; induction ys; intros; [destruct xs; [apply JsRecordRel_nil | destruct p as [kx vx]; specialize (H1 kx); assert_specialize H1; [apply List.Exists_cons_hd; reflexivity | inv H1]] |]; destruct a as [k vy].
  assert (JsRecordHasKey k xs); [apply H1; apply List.Exists_cons_hd; reflexivity |].
  apply JsRecordAdd_from_HasKey in H3; [| assumption]; destruct H3 as [vx [xs0 H3]]; inv H0.
  apply JsRecordRel_cons with vx xs0; [apply H2 with k | apply IHys | assumption | assumption].
  - apply JsRecordAdd_In with xs0; assumption.
  - left; reflexivity.
  - eapply proj2; apply JsRecordAdd_NoDup_rev with vx xs; [assumption | exact H3].
  - assumption.
  - intros; specialize (H1 k0); destruct (string_dec k0 k); subst; split; intros.
    + apply JsRecordAdd_not_HasKey in H3; contradiction.
    + contradiction.
    + eapply JsRecordHasKey_uncons1; [apply H1 | exact n]; apply JsRecordAdd_HasKey0 with k vx xs0; assumption.
    + antisymmetry in n; apply JsRecordAdd_HasKey1 with k vx xs; try assumption; apply H1; apply List.Exists_cons_tl; assumption.
  - intros; specialize (H2 k0 vx0 vy0); destruct (string_dec k0 k); [| apply H2].
    + subst; contradict H8; apply JsRecordHasKey_In0 with vy0; assumption.
    + apply JsRecordAdd_In0 with k vx xs0; assumption.
    + right; assumption.
Qed.

Theorem JsRecord1Rel_In0: forall {A: Set} {rel: relation A} (xs ys: js_record A),
    JsRecordNoDup xs -> JsRecordNoDup ys -> (forall k, JsRecordHasKey k ys -> JsRecordHasKey k xs) ->
    (forall (k: string) (vx vy: A), List.In (k, vx) xs -> List.In (k, vy) ys -> rel vx vy) ->
    JsRecord1Rel rel xs ys.
Proof.
  induction xs; intros; [destruct ys; [apply JsRecord1Rel_nil; constructor | destruct p as [ky vy]; specialize (H1 ky); assert_specialize H1; [apply List.Exists_cons_hd; reflexivity | inv H1]] |]; destruct a as [k vx].
  destruct (JsRecordHasKey_dec k ys).
  - apply JsRecordAdd_from_HasKey in H3; [| assumption]; destruct H3 as [vy [ys0 H3]]; inv H.
    apply JsRecord1Rel_cons with vy ys0; [apply H2 with k | apply IHxs | ..]; try assumption.
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
  - inv H; apply JsRecord1Rel_cons_l; [apply IHxs | |]; try assumption.
    + intros; specialize (H1 k0 H); inv H1; [contradiction | assumption].
    + intros; specialize (H2 k0 vx0 vy); destruct (string_dec k0 k); [| apply H2].
      * subst; contradict H8; apply JsRecordHasKey_In0 with vx0; assumption.
      * right; assumption.
      * assumption.
Qed.

Theorem JsRecordEqKeys_nil : forall {A: Type}, JsRecordEqKeys (@nil (string * A)) nil.
Proof.
  intros A k; split; intros; exact H.
Qed.

Theorem JsRecordEqKeys_not_cons_nil : forall {A: Type} (x: string * A) (xs: js_record A), ~JsRecordEqKeys (x :: xs)%list nil.
Proof.
  intros. intros H. destruct x as [kx vx]. specialize (H kx). assert_specialize H; [apply List.Exists_cons_hd; reflexivity |]. inv H.
Qed.

Theorem JsRecordEqKeys_not_nil_cons : forall {A: Type} (y: string * A) (ys: js_record A), ~JsRecordEqKeys nil (y :: ys)%list.
Proof.
  intros. intros H. destruct y as [ky vy]. specialize (H ky). destruct H as [_ H]. assert_specialize H; [apply List.Exists_cons_hd; reflexivity |]. inv H.
Qed.

Theorem js_record_ind : forall {A: Type} (P: js_record A -> Prop),
    P nil ->
    (forall xs xs', P xs -> (exists kx vx, ~JsRecordHasKey kx xs -> JsRecordAdd kx vx xs xs') -> P xs') ->
    forall xs, P xs.
Proof.
  intros A P P0 Pn xs. induction xs; [exact P0 | apply (Pn xs); [exact IHxs |]]. destruct a as [kx vx]. exists kx. exists vx. apply JsRecordAdd_head.
Qed.
