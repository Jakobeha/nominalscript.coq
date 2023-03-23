(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Notation "a <| b" := (a b) (at level 102, right associativity, only parsing).
Notation "a << b" := (fun x => a (b x)) (at level 101, right associativity, only parsing).

Definition cons_opt {A: Type} (x: option A) (xs: list A) :=
match x with
| None => xs
| Some x => cons x xs
end.

Notation "x ?:: xs" := (cons_opt x xs) (at level 60, right associativity): list_scope.

Definition unwrap_or {A: Type} (default: A) (a: option A): A :=
match a with
| None => default
| Some a => a
end.

Definition is_empty {A: Type} (xs : list A) : bool :=
match xs with
| nil => true
| cons x xs' => false
end.

Fixpoint all {A: Type} (pred: A -> bool) (xs: list A): bool :=
match xs with
| nil => true
| cons x xs' => pred x && all pred xs'
end.

Fixpoint any {A: Type} (p: A -> bool) (xs: list A): bool :=
match xs with
| nil => false
| cons x xs => p x || any p xs
end.

Definition map := List.map.
Definition fold := List.fold_right.
Definition len := List.length.
Definition find := List.find.

Fixpoint find_map {A B: Type} (p: A -> option B) (xs: list A): option B :=
match xs with
| nil => None
| cons x xs =>
    match p x with
    | None => find_map p xs
    | Some y => Some y
    end
end.

Fixpoint filter_map {A B: Type} (p: A -> option B) (xs: list A): list B :=
match xs with
| nil => nil
| cons x xs => cons_opt (p x) (filter_map p xs)
end.

Fixpoint zip_eqb {A B: Type} (eqb: A -> B -> bool) (xs: list A) (ys: list B): bool :=
match xs, ys with
| cons x xs, cons y ys => eqb x y && zip_eqb eqb xs ys
| _, _ => true
end.

Fixpoint zip_with {A B C: Type} (f: A -> B -> C) (xs: list A) (ys: list B): list C :=
match xs, ys with
| cons x xs, cons y ys => cons (f x y) (zip_with f xs ys)
| _, _ => nil
end.

Fixpoint intersect {A B C: Type} (intersect1: A -> B -> option C) (xs: list A) (ys: list B): list C :=
match xs with
| nil => nil
| cons x xs => cons_opt (find_map (intersect1 x) ys) (intersect intersect1 xs ys)
end.

Definition subtract_hd {A: Type} (eqb: A -> A -> bool) (xs: list A) (ys: list A): option A :=
  find (fun x => negb (any (eqb x) ys)) xs.

Definition list_sum: list nat -> nat := fold Nat.add 0.
Definition list_max: list nat -> nat := fold Nat.max 0.

Definition option_sum (a: option nat): nat :=
match a with
| None => 0
| Some a => a
end.

Definition option_max (a: option nat): nat :=
match a with
| None => 0
| Some a => a
end.
Definition is_some {A: Type} (a: option A): bool :=
match a with
| None => false
| Some _ => true
end.

Definition option_zip_with {A B C: Type} (f: A -> B -> C) (a: option A) (b: option B): option C :=
match a, b with
| Some a, Some b => Some (f a b)
| _, _ => None
end.

Inductive Option_Forall {A: Type}: (A -> Prop) -> option A -> Prop :=
| Option_Forall_None: forall (P: A -> Prop), Option_Forall P None
| Option_Forall_Some: forall (P: A -> Prop) (a: A), P a -> Option_Forall P (Some a).

Definition js_record (A: Set): Set := list (string * A).

Fixpoint js_record_has_key {A: Set} (key: string) (a: js_record A): bool :=
match a with
| nil => false
| cons (x_key, _) xs => String.eqb key x_key || js_record_has_key key xs
end.

Fixpoint js_record_assoc {A: Set} (key: string) (a: js_record A): option A :=
match a with
| nil => None
| cons (x_key, x) xs => if String.eqb key x_key then Some x else js_record_assoc key xs
end.

Definition map_js_record {A B: Set} (f: A -> B) (a: js_record A): js_record B :=
  List.map (fun x => match x with (name, value) => (name, f value) end) a.

Fixpoint js_record_fields_superset {A B: Set} (a: js_record A) (b: js_record B): bool :=
match b with
| nil => true
| cons (b_key, _) bs => js_record_has_key b_key a && js_record_fields_superset a bs
end.

Definition js_record_fields_eqb {A B: Set} (a: js_record A) (b: js_record B): bool :=
  js_record_fields_superset a b && js_record_fields_superset b a.

Fixpoint js_record_zip_with {A B C: Set} (f: A -> B -> C) (a: js_record A) (b: js_record B): js_record C :=
match a with
| nil => nil
| cons (x_key, x) xs =>
    cons_opt (option_map ((fun z => (x_key, z)) << f x) (js_record_assoc x_key b)) (js_record_zip_with f xs b)
end.

Definition JsRecordForall {A: Set} (P: A -> Prop) : js_record A -> Prop := List.Forall (P << snd).

Definition JsRecordHasKey {A: Set} (key: string): js_record A -> Prop :=
  List.Exists (fun '(key', _) => key = key').

Definition JsRecordSuperKeys {A: Set} (xs ys: js_record A): Prop :=
  forall k, JsRecordHasKey k xs -> JsRecordHasKey k ys.

Definition JsRecordEqKeys {A: Set} (xs ys: js_record A): Prop :=
  forall k, JsRecordHasKey k xs <-> JsRecordHasKey k ys.

Inductive JsRecordEqKeys0 {A: Set}: js_record A -> js_record A -> Prop :=
| JsRecordEqKeys0_nil : JsRecordEqKeys0 nil nil
| JsRecordEqKeys0_add : forall (k: string) (vx vy: A) (xs ys xs' ys': js_record A), JsRecordEqKeys0 xs ys -> List.Add (k, vx) xs xs' -> List.Add (k, vy) ys ys' -> JsRecordEqKeys0 xs' ys'
.

Inductive JsRecordAdd {A: Set} (kx: string) (vx: A) : js_record A -> js_record A -> Prop :=
| JsRecordAdd_head : forall (xs: js_record A), JsRecordAdd kx vx xs ((kx, vx) :: xs)%list
| JsRecordAdd_cons : forall (kx0: string) (vx0: A) (xs xs': js_record A), kx0 <> kx -> JsRecordAdd kx vx xs xs' -> JsRecordAdd kx vx ((kx0, vx0) :: xs)%list ((kx0, vx0) :: xs')%list
.

Inductive JsRecordNoDup {A: Set} : js_record A -> Prop :=
| JsRecordNoDup_nil : JsRecordNoDup nil
| JsRecordNoDup_cons : forall kx vx xs, JsRecordNoDup xs -> not (JsRecordHasKey kx xs) -> JsRecordNoDup ((kx, vx) :: xs)%list
.

Theorem nat_ind2: forall (P: nat -> nat -> Prop),
    P 0 0 ->
    (forall x, P x 0 -> P (S x) 0) ->
    (forall y, P 0 y -> P 0 (S y)) ->
    (forall x y, P x y -> P (S x) (S y)) ->
    forall x y, P x y.
Proof.
  intros P P0 Px Py Pxy x.
  induction x; intros y; induction y.
  - exact P0.
  - apply Py.
    exact IHy.
  - apply Px.
    exact (IHx 0).
  - apply Pxy.
    exact (IHx y).
Qed.

Ltac ind_nat2 x y :=
  revert x y;
  match goal with
  | [ |- forall x y, ?H ] => apply (nat_ind2 (fun x y => H))
  end.

Theorem list_ind2: forall {A B: Type} (P: list A -> list B -> Prop),
    P nil nil ->
    (forall x xs, P xs nil -> P (cons x xs) nil) ->
    (forall y ys, P nil ys -> P nil (cons y ys)) ->
    (forall x y xs ys, P xs ys -> P (cons x xs) (cons y ys)) ->
    forall xs ys, P xs ys.
Proof.
  intros A B P P0 Px Py Pxy xs.
  induction xs; intros ys; induction ys.
  - exact P0.
  - apply Py.
    exact IHys.
  - apply Px.
    exact (IHxs nil).
  - apply Pxy.
    exact (IHxs ys).
Qed.

Ltac ind_list2 x y :=
  revert x y;
  match goal with
  | [ |- forall x y, ?H ] => apply (list_ind2 (fun x y => H))
  end.

Theorem list_ind2_alt: forall {A B: Type} (P: list A -> list B -> Prop),
    P nil nil ->
    (forall x xs ys, P xs ys -> P (cons x xs) ys) ->
    (forall y xs ys, P xs ys -> P xs (cons y ys)) ->
    forall xs ys, P xs ys.
Proof.
  intros A B P P0 Px Py xs.
  induction xs; intros ys; induction ys.
  - exact P0.
  - apply Py.
    exact IHys.
  - apply Px.
    exact (IHxs nil).
  - apply Py.
    exact IHys.
Qed.

Ltac ind_list2_alt x y :=
  revert x y;
  match goal with
  | [ |- forall x y, ?H ] => apply (list_ind2_alt (fun x y => H))
  end.

Ltac by_ tactic := tactic; reflexivity.
Ltac remove_existTs :=
  repeat lazymatch goal with
  | H : existT (fun x0 : Set => x0) ?T ?a = existT (fun x1 : Set => x1) ?T ?b |- _ => apply inj_pair2 in H
  | H : existT (fun x0 : Set => x0) ?A ?a = existT (fun x1 : Set => x1) ?B ?b |- _ => apply eq_sigT_fst in H
  end.
Ltac inv H := inversion H; remove_existTs; subst; clear H; try discriminate.
Ltac if_some tac H := lazymatch H with | None => idtac | @None => idtac | Some ?H => tac H | ?H => idtac H; fail "must be None or Some" end.

Ltac fix_js_record_existTs :=
  repeat match goal with
  | H : existT (fun x0 : Set => x0) (js_record ?T) ?a =
        existT (fun x1 : Set => x1) (list (string * ?T)) ?b |- _ =>
      unfold js_record in H; apply inj_pair2 in H; subst
  | H : existT (fun x0 : Set => x0) (list (string * ?T)) ?a =
        existT (fun x1 : Set => x1) (js_record ?T) ?b |- _ =>
      unfold js_record in H; apply inj_pair2 in H; subst
  end.

Ltac clear_obvious :=
  repeat lazymatch goal with
  | H : ?T = ?T |- _ => clear H
  | H : True |- _ => clear H
  end.

Ltac invert_eqs :=
  repeat lazymatch goal with
  | H : ?f ?a ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 = ?f ?b ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 |- _ => inv H
  | H : ?f ?a ?a0 ?a1 ?a2 ?a3 ?a4 = ?f ?b ?b0 ?b1 ?b2 ?b3 ?b4 |- _ => inv H
  | H : ?f ?a ?a0 ?a1 ?a2 ?a3 = ?f ?b ?b0 ?b1 ?b2 ?b3 |- _ => inv H
  | H : ?f ?a ?a0 ?a1 ?a2 = ?f ?b ?b0 ?b1 ?b2 |- _ => inv H
  | H : ?f ?a ?a0 ?a1 = ?f ?b ?b0 ?b1 |- _ => inv H
  | H : ?f ?a ?a0 = ?f ?b ?b0 |- _ => inv H
  | H : ?f ?a = ?f ?b |- _ => inv H
  | H : ?a = nil |- _ => rewrite H in *; clear H
  end.

Ltac revert_with t :=
  repeat lazymatch goal with
  | H : context[t] |- _ => revert H
  end.

Ltac assert_specialize H :=
  let tH := type of H in
  match tH with
  | ?tHH -> ?tHC =>
      let HH := fresh "HH" in
      assert (HH : tHH); [clear H | specialize (H HH); clear HH]
  | ?tHH <-> ?tHC => apply proj1 in H; assert_specialize H
  end.

Ltac split_with H :=
  split; [destruct H as [H _] | destruct H as [_ H]].

Ltac left_right_with H :=
  destruct H as [H | H]; [left | right].

Lemma list_add_ind : forall {A: Type} (P: list A -> Prop),
    P nil ->
    (forall xs xs', P xs -> (exists x, List.Add x xs xs') -> P xs') ->
    forall xs, P xs.
Proof.
  intros A P P0 Pn xs; induction xs; [exact P0 | apply (Pn xs); [exact IHxs |]]. exists a. apply List.Add_head.
Qed.

Ltac rewrite_Forall_Exists_neg A key :=
  let H := fresh "H" in
  replace (fun '(key', _) => key <> key') with (fun (x: string * A) => not ((fun '(key', _) => key = key') x)) in *;
  try (apply functional_extensionality; intros H; destruct H; reflexivity);
  rewrite List.Forall_Exists_neg in *.

Theorem JsRecordHasKey_dec: forall {A: Set} (key: string) (xs: js_record A),
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

Theorem JsRecordHasKey_neg: forall {A: Set} (key: string) (xs: js_record A),
    not (JsRecordHasKey key xs) <-> List.Forall (fun '(key', _) => key <> key') xs.
Proof.
  split; intros; rewrite_Forall_Exists_neg A key; exact H.
Qed.

Theorem JsRecordHasKey_alt: forall {A: Set} (key: string) (xs: js_record A),
    JsRecordHasKey key xs <-> not (List.Forall (fun '(key', _) => key <> key') xs).
Proof.
  split; intros; rewrite_Forall_Exists_neg A key.
  - intros H0; contradiction (H0 H).
  - apply Decidable.not_not; unfold Decidable.decidable; [apply JsRecordHasKey_dec | exact H].
Qed.

Theorem JsRecordHasKey_neg_Add : forall {A: Set} (kx' : string) (xs': js_record A),
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

Corollary JsRecordHasKey_neg_Add0 : forall {A: Set} (kx' : string) (xs': js_record A),
  not (JsRecordHasKey kx' xs') ->
  forall (kx: string) (vx: A) (xs: js_record A),
  List.Add (kx, vx) xs xs' ->
  not (JsRecordHasKey kx' xs).
Proof.
  intros; eapply proj2; eapply JsRecordHasKey_neg_Add; [exact H | exact H0].
Qed.

Lemma JsRecordNoDup_alt0 : forall {A: Set} (xs': js_record A),
  JsRecordNoDup xs' ->
  forall (kx: string) (vx: A) (xs: js_record A),
  List.Add (kx, vx) xs xs' ->
  JsRecordNoDup xs.
Proof.
  intros A xs'; induction xs'; intros; inv H0; inv H; [exact H2 |]; apply JsRecordNoDup_cons.
  - apply (IHxs' H2 kx vx); exact H3.
  - eapply (JsRecordHasKey_neg_Add0 H4); exact H3.
Qed.

Lemma JsRecordNoDup_alt1 : forall {A: Set} (xs': js_record A),
  JsRecordNoDup xs' ->
  forall (kx: string) (vx: A) (xs: js_record A),
  List.Add (kx, vx) xs xs' ->
  not (JsRecordHasKey kx xs).
Proof.
  intros A xs'; induction xs'; intros; inv H0; inv H; [exact H4 |]; rewrite JsRecordHasKey_neg; apply List.Forall_cons.
  - intros H; subst; rewrite JsRecordHasKey_neg, List.Forall_forall in H4; pose (H := List.Add_in H3); pose (H0 := List.in_eq (kx0, vx) l); rewrite <- H in H0; specialize (H4 _ H0); simpl in H4; contradiction (H4 eq_refl).
  - rewrite <- JsRecordHasKey_neg. eapply IHxs'; [exact H2 | exact H3].
Qed.

Theorem JsRecordNoDup_alt : forall {A: Set} (kx: string) (vx: A) (xs xs': js_record A),
  JsRecordNoDup xs' ->
  List.Add (kx, vx) xs xs' ->
  JsRecordNoDup xs /\ not (JsRecordHasKey kx xs).
Proof.
  split; [eapply JsRecordNoDup_alt0 | eapply JsRecordNoDup_alt1]; [exact H | exact H0 | exact H | exact H0].
Qed.

Theorem JsRecordAdd_HasKey : forall {A: Set} (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> JsRecordHasKey kx xs'.
Proof.
  intros. induction H; [apply List.Exists_cons_hd; reflexivity | apply List.Exists_cons_tl; exact IHJsRecordAdd].
Qed.

Theorem JsRecordAdd_ListAdd : forall {A: Set} (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> List.Add (kx, vx) xs xs'.
Proof.
  intros. induction H; constructor. exact IHJsRecordAdd.
Qed.

Theorem JsRecordAdd_Forall : forall {A: Set} (P: A -> Prop) (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' -> JsRecordForall P xs' -> P vx /\ JsRecordForall P xs.
Proof.
  intros. apply JsRecordAdd_ListAdd in H. unfold JsRecordForall in *. rewrite List.Forall_forall in *. split.
  - specialize (H0 (kx, vx)). simpl in H0. apply H0. rewrite (List.Add_in H). simpl. left. reflexivity.
  - intros. specialize (H0 x). destruct x as [kx0 vx0]. simpl in *. apply H0. rewrite (List.Add_in H). simpl. right. exact H1.
Qed.

Theorem js_record_ind : forall {A: Set} (P: js_record A -> Prop),
    P nil ->
    (forall xs xs', P xs -> (exists kx vx, JsRecordAdd kx vx xs xs') -> P xs') ->
    forall xs, P xs.
Proof.
  intros A P P0 Pn xs. induction xs; [exact P0 | apply (Pn xs); [exact IHxs |]]. destruct a as [kx vx]. exists kx. exists vx. apply JsRecordAdd_head.
Qed.

Theorem js_record_ind2_dumb : forall {A: Set} (P: js_record A -> js_record A -> Prop),
    P nil nil ->
    (forall xs xs', P xs nil -> (exists kx vx, JsRecordAdd kx vx xs xs') -> P xs' nil) ->
    (forall ys ys', P nil ys -> (exists ky vy, JsRecordAdd ky vy ys ys') -> P nil ys') ->
    (forall xs ys xs' ys', P xs ys -> (exists kx vx, JsRecordAdd kx vx xs xs') -> (exists ky vy, JsRecordAdd ky vy ys ys') -> P xs' ys') ->
    forall xs ys, P xs ys.
Proof.
  intros A P P0 Px Py Pxy xs. induction xs; intros; induction ys; [exact P0 | apply (Py ys); [exact IHys |] | apply (Px xs); [exact (IHxs nil) |] | apply (Pxy xs ys); [exact (IHxs ys) | |] ].
  - destruct a as [ky vy]. exists ky. exists vy. apply JsRecordAdd_head.
  - destruct a as [kx vx]. exists kx. exists vx. apply JsRecordAdd_head.
  - destruct a as [kx vx]. destruct a0 as [ky vy]. exists kx. exists vx. apply JsRecordAdd_head.
  - destruct a as [kx vx]. destruct a0 as [ky vy]. exists ky. exists vy. apply JsRecordAdd_head.
Qed.

Ltac ind_js_record2_dumb x y :=
  revert x y;
  match goal with
  | [ |- forall x y, ?H ] => apply (js_record_ind2_dumb (fun x y => H))
  end.

Theorem JsRecordEqKeys_nil : forall {A: Set}, JsRecordEqKeys (@nil (string * A)) nil.
Proof.
  intros A k; split; intros; exact H.
Qed.

Theorem JsRecordEqKeys_not_cons_nil : forall {A: Set} (x: string * A) (xs: js_record A), ~JsRecordEqKeys (x :: xs)%list nil.
Proof.
  intros. intros H. destruct x as [kx vx]. specialize (H kx). assert_specialize H; [apply List.Exists_cons_hd; reflexivity |]. inv H.
Qed.

Theorem JsRecordEqKeys_not_nil_cons : forall {A: Set} (y: string * A) (ys: js_record A), ~JsRecordEqKeys nil (y :: ys)%list.
Proof.
  intros. intros H. destruct y as [ky vy]. specialize (H ky). destruct H as [_ H]. assert_specialize H; [apply List.Exists_cons_hd; reflexivity |]. inv H.
Qed.

Theorem JsRecordEqKeys_cons : forall {A: Set} (k: string) (vx vy: A) (xs ys: js_record A),
    JsRecordEqKeys xs ys <-> JsRecordEqKeys ((k, vx) :: xs)%list ((k, vy) :: ys)%list.
      (* * intros k. split; intros.
        all: inv H0; [apply List.Exists_cons_hd; reflexivity | apply List.Exists_cons_tl]; apply H; exact H2.
      * intros H0. contradict H. intros k. split; intros.
        --  assert (JsRecordHasKey k ((ky, vx) :: xs)%list); [apply List.Exists_cons_tl; exact H |].
            apply H0 in H1. apply List.Exists_cons in H1. destruct H1.
            ++  subst. *)
Admitted.

Theorem JsRecordEqKeys_add : forall {A: Set} (k: string) (vx vy: A) (xs ys xs' ys': js_record A),
    List.Add (k, vx) xs xs' -> List.Add (k, vy) ys ys' -> (JsRecordEqKeys xs ys <-> JsRecordEqKeys xs' ys').
      (* * intros k. split; intros.
        all: inv H0; [apply List.Exists_cons_hd; reflexivity | apply List.Exists_cons_tl]; apply H; exact H2.
      * intros H0. contradict H. intros k. split; intros.
        --  assert (JsRecordHasKey k ((ky, vx) :: xs)%list); [apply List.Exists_cons_tl; exact H |].
            apply H0 in H1. apply List.Exists_cons in H1. destruct H1.
            ++  subst. *)
Admitted.

Theorem JsRecordAdd_destruct : forall {A: Set} (kx: string) (vx: A) (xs xs': js_record A),
    JsRecordAdd kx vx xs xs' <-> (List.Add (kx, vx) xs xs' /\ ~JsRecordHasKey kx xs).
Admitted.

Theorem JsRecordEqKeys_0 : forall {A: Set} (xs ys: js_record A), JsRecordEqKeys xs ys <-> JsRecordEqKeys0 xs ys.
Proof.
  intros; ind_js_record2_dumb xs ys; split; intros.
  - constructor.
  - apply JsRecordEqKeys_nil.
  - destruct xs'; [apply JsRecordEqKeys0_nil | apply JsRecordEqKeys_not_cons_nil in H1; contradiction H1].
  - destruct xs'; [apply JsRecordEqKeys_nil | inv H1; inv H4].
  - destruct ys'; [apply JsRecordEqKeys0_nil | apply JsRecordEqKeys_not_nil_cons in H1; contradiction H1].
  - destruct ys'; [apply JsRecordEqKeys_nil | inv H1; inv H3].
  - destruct H0 as [kx [vx H0]]; destruct H1 as [ky [vy H1]]. apply JsRecordAdd_destruct in H0. apply JsRecordAdd_destruct in H1. destruct H0. destruct H1. destruct (string_dec kx ky).
    + subst. clear H3. clear H4. eapply JsRecordEqKeys0_add; [apply H | exact H0 | exact H1]. apply (JsRecordEqKeys_add H0 H1). exact H2.
    +
Admitted.

Theorem JsRecordEqKeys_sub_cons : forall {A: Set} (kx ky: string) (vx vy: A) (xs ys: js_record A),
    JsRecordEqKeys xs ys -> (JsRecordEqKeys ((kx, vx) :: xs)%list ((ky, vy) :: ys)%list <-> kx = ky).
Admitted.

Theorem JsRecordEqKeys_dec : forall {A: Set} (xs ys: js_record A),
    JsRecordEqKeys xs ys \/ not (JsRecordEqKeys xs ys).
Proof.
  intros. ind_list2 xs ys; intros.
  - left. apply JsRecordEqKeys_nil.
  - right. apply JsRecordEqKeys_not_cons_nil.
  - right. apply JsRecordEqKeys_not_nil_cons.
  - destruct x as [kx vx]. destruct y as [ky vy]. destruct (string_dec kx ky).
    + subst. left_right_with H.
      * apply JsRecordEqKeys_cons. exact H.
      * intros H0. apply JsRecordEqKeys_cons in H0. contradiction (H H0).
    + right. intros H0. destruct H.
      *
      specialize (H0 kx). assert_specialize H0; [apply List.Exists_cons_hd; reflexivity |].
      inv H0; [contradiction (n eq_refl) |].
Admitted.

Theorem js_record_ind2 : forall {A: Set} (P: js_record A -> js_record A -> Prop),
    P nil nil ->
    (forall xs xs', P xs nil -> (exists kx vx, JsRecordAdd kx vx xs xs') -> P xs' nil) ->
    (forall ys ys', P nil ys -> (exists ky vy, JsRecordAdd ky vy ys ys') -> P nil ys') ->
    (forall xs ys xs' ys', P xs ys -> (JsRecordEqKeys xs ys -> JsRecordEqKeys xs' ys') -> (exists k, (exists vx, JsRecordAdd k vx xs xs') /\ (exists vy, JsRecordAdd k vy ys ys')) -> P xs' ys') ->
    forall xs ys, P xs ys.
Admitted.

Ltac ind_js_record2 x y :=
  revert x y;
  match goal with
  | [ |- forall x y, ?H ] => apply (js_record_ind2 (fun x y => H))
  end.
