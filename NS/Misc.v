(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

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

Lemma nat_ind2: forall (P: nat -> nat -> Prop),
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

Lemma list_ind2: forall {A B: Type} (P: list A -> list B -> Prop),
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

Ltac by_ tactic := tactic; reflexivity.
Ltac inv H := inversion H; subst; clear H.

Ltac assert_specialize H :=
  let tH := type of H in
  match tH with
  | ?tHH -> ?tHC =>
      let HH := fresh "HH" in
      assert (HH : tHH); [clear H | specialize (H HH); clear HH]
  end.

Ltac split_with H :=
  split; [destruct H as [H _] | destruct H as [_ H]].

Ltac left_right_with H :=
  destruct H as [H | H]; [left | right].
