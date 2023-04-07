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

Inductive JsRecordRel {A: Type} (rel: relation A): relation (js_record A) :=
| JsRecordRel_nil : JsRecordRel rel nil nil
| JsRecordRel_cons : forall (k: string) (vx vy: A) (xs xs' ys: js_record A),
    rel vx vy -> JsRecordRel rel xs ys -> JsRecordAdd k vx xs xs' -> ~ JsRecordHasKey k ys -> JsRecordRel rel xs' ((k, vy) :: ys)%list
.

Inductive JsRecordNoDup {A: Type} : js_record A -> Prop :=
| JsRecordNoDup_nil : JsRecordNoDup nil
| JsRecordNoDup_cons : forall kx vx xs, JsRecordNoDup xs -> not (JsRecordHasKey kx xs) -> JsRecordNoDup ((kx, vx) :: xs)%list
.

Inductive JsRecordNoDupForall {A: Type} (P: A -> Prop): js_record A -> Prop :=
| JsRecordNoDupForall_nil : JsRecordNoDupForall P nil
| JsRecordNoDupForall_cons : forall kx vx xs, JsRecordNoDupForall P xs -> ~ JsRecordHasKey kx xs -> P vx -> JsRecordNoDupForall P ((kx, vx) :: xs)%list
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

Lemma JsRecordNoDup_alt0 : forall {A: Type} (xs': js_record A),
  JsRecordNoDup xs' ->
  forall (kx: string) (vx: A) (xs: js_record A),
  List.Add (kx, vx) xs xs' ->
  JsRecordNoDup xs.
Proof.
  intros A xs'; induction xs'; intros; inv H0; inv H; [exact H2 |]; apply JsRecordNoDup_cons.
  - apply (IHxs' H2 kx vx); exact H3.
  - eapply (JsRecordHasKey_neg_Add0 H4); exact H3.
Qed.

Lemma JsRecordNoDup_alt1 : forall {A: Type} (xs': js_record A),
  JsRecordNoDup xs' ->
  forall (kx: string) (vx: A) (xs: js_record A),
  List.Add (kx, vx) xs xs' ->
  not (JsRecordHasKey kx xs).
Proof.
  intros A xs'; induction xs'; intros; inv H0; inv H; [exact H4 |]; rewrite JsRecordHasKey_neg; apply List.Forall_cons.
  - intros H; subst; rewrite JsRecordHasKey_neg, List.Forall_forall in H4; pose (H := List.Add_in H3); pose (H0 := List.in_eq (kx0, vx) l); rewrite <- H in H0; specialize (H4 _ H0); simpl in H4; contradiction (H4 eq_refl).
  - rewrite <- JsRecordHasKey_neg. eapply IHxs'; [exact H2 | exact H3].
Qed.

Theorem JsRecordNoDup_alt : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
  JsRecordNoDup xs' ->
  List.Add (kx, vx) xs xs' ->
  JsRecordNoDup xs /\ not (JsRecordHasKey kx xs).
Proof.
  split; [eapply JsRecordNoDup_alt0 | eapply JsRecordNoDup_alt1]; [exact H | exact H0 | exact H | exact H0].
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

Theorem JsRecordAdd_not_HasKey : forall {A: Type} (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> ~ JsRecordHasKey kx xs.
Proof.
  intros; induction H; [exact H |]; intros n; inv n; [contradiction H; reflexivity |]; contradiction IHJsRecordAdd.
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

Theorem JsRecordRel_eq_refl : forall {A: Type} (xs: js_record A), JsRecordNoDup xs -> JsRecordRel eq xs xs.
Proof.
  intros; induction xs; [| destruct a as [kx vx]]; econstructor; inv H; [reflexivity | apply IHxs | apply JsRecordAdd_head |]; assumption.
Qed.

Theorem JsRecordAdd_join_orig: forall {A: Type} (kx: string) (vx vx0: A) (xs xs0 xs': js_record A),
    JsRecordNoDup xs' ->
    JsRecordAdd kx vx xs xs' ->
    JsRecordAdd kx vx0 xs0 xs' ->
    JsRecordRel eq xs xs0.
Proof.
  intros; induction xs'; [inv H0 |]; destruct a as [kx' vx']; inv H H0 H1; [apply JsRecordRel_eq_refl; assumption | contradiction H5; reflexivity | contradiction H5; reflexivity |].
  apply IHxs'; [exact H4 | ..].

  destruct xs'; [inv H6 |]; destruct p as [kx'0 vx'0].
  apply IHxs'.
  - apply JsRecordAdd_cons.
  f_equal; [exact (IHxs' H2 H3) |].
  -
Qed.
Ltac join_key_JsRecordAdd H H0 := remember (JsRecordAdd_join_key H H0) eqn:x; clear x; subst.

Theorem JsRecordRel_In: forall {A: Set} {rel: relation A} (k: string) (vx vy: A) (xs ys: js_record A),
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

Theorem JsRecordRel_add: forall {A: Set} {rel: relation A} (k: string) (vx vy: A) (xs xs' ys ys': js_record A),
    JsRecordAdd k vx xs xs' -> JsRecordAdd k vy ys ys' -> JsRecordRel rel xs' ys' -> rel vx vy.
Proof.
  intros. apply JsRecordAdd_In in H, H0; eapply JsRecordRel_In in H1; [exact H1 | exact H | exact H0].
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
