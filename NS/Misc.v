(* Add LoadPath should not be necessary but it is *)
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
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

Inductive Option_Forall {A: Type} (P: A -> Prop): option A -> Prop :=
| Option_Forall_None: Option_Forall P None
| Option_Forall_Some: forall a, P a -> Option_Forall P (Some a).

Ltac remove_existTs :=
  repeat lazymatch goal with
  | H : existT (fun x0 : Set => x0) ?T ?a = existT (fun x1 : Set => x1) ?T ?b |- _ => apply inj_pair2 in H
  end.
Ltac clear_obvious :=
  repeat lazymatch goal with
  | H : ?T = ?T |- _ => clear H
  | H : True |- _ => clear H
  end.
Ltac _inv H := inversion H; remove_existTs; clear_obvious; subst; clear H; try discriminate.
Tactic Notation "inv" hyp(H) := _inv H.
Tactic Notation "inv" hyp(H) hyp(H0) := _inv H; _inv H0.
Tactic Notation "inv" hyp(H) hyp(H0) hyp(H1) := _inv H; _inv H0; _inv H1.
Tactic Notation "inv" hyp(H) hyp(H0) hyp(H1) hyp(H2) := _inv H; _inv H0; _inv H1; _inv H2.
Tactic Notation "inv" hyp(H) hyp(H0) hyp(H1) hyp(H2) hyp(H3) := _inv H; _inv H0; _inv H1; _inv H2; _inv H3.
Tactic Notation "inv" hyp(H) hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4) := _inv H; _inv H0; _inv H1; _inv H2; _inv H3; _inv H4.
Tactic Notation "inv" hyp(H) hyp(H0) hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5) := _inv H; _inv H0; _inv H1; _inv H2; _inv H3; _inv H4; _inv H5.
Ltac if_some tac H := lazymatch H with | None => idtac | @None => idtac | Some ?H => tac H | ?H => idtac H; fail "must be None or Some" end.

Local Ltac invert_eqs' n :=
  match n with
  | 0 => idtac "warning: invert_eqs' gave up"
  | S ?n =>
      lazymatch goal with
      | H : ?f ?a ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 = ?f ?b ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 |- _ => inv H; invert_eqs' n
      | H : ?f ?a ?a0 ?a1 ?a2 ?a3 ?a4 = ?f ?b ?b0 ?b1 ?b2 ?b3 ?b4 |- _ => inv H; invert_eqs' n
      | H : ?f ?a ?a0 ?a1 ?a2 ?a3 = ?f ?b ?b0 ?b1 ?b2 ?b3 |- _ => inv H; invert_eqs' n
      | H : ?f ?a ?a0 ?a1 ?a2 = ?f ?b ?b0 ?b1 ?b2 |- _ => inv H; invert_eqs' n
      | H : ?f ?a ?a0 ?a1 = ?f ?b ?b0 ?b1 |- _ => inv H; invert_eqs' n
      | H : ?f ?a ?a0 = ?f ?b ?b0 |- _ => inv H; invert_eqs' n
      | H : ?f ?a = ?f ?b |- _ => inv H; invert_eqs' n
      | H : ?a = nil |- _ => rewrite H in *; clear H; invert_eqs' n
      end
  end.
Ltac invert_eqs := invert_eqs' 33.

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

Tactic Notation "antisymmetry" :=
  lazymatch goal with
  | |- ?a <> ?b => assert (n : b <> a); [| intros e; symmetry in e; contradiction (n e)]
  | _ => fail "not a contradiction"
  end.

Tactic Notation "antisymmetry" "in" hyp(n) :=
  lazymatch type of n with
  | ?a <> ?b => assert (n' : b <> a); [intros e; symmetry in e; exact (n e) | clear n; rename n' into n]
  | _ => fail "not a contradiction"
  end.

Ltac split' := repeat split.

Ltac split_with H :=
  split; [destruct H as [H _] | destruct H as [_ H]].

Ltac left_right_with H :=
  destruct H as [H | H]; [left | right].

Ltac destruct_var H := is_var H; destruct H.

Tactic Notation "pose'" constr(x) "as" ident(id) := pose (id := x); clearbody id.
Tactic Notation "pose'" constr(x) := let e := fresh "e" in pose' x as e.

Ltac destruct' H :=
  destruct_var H || lazymatch H with
  | ?P ?H0 ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 ?H7 => is_ind P; destruct' H0; destruct' H1; destruct' H2; destruct' H3; destruct' H4; destruct' H5; destruct' H6; destruct' H7
  | ?P ?H0 ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 => is_ind P; destruct' H0; destruct' H1; destruct' H2; destruct' H3; destruct' H4; destruct' H5; destruct' H6
  | ?P ?H0 ?H1 ?H2 ?H3 ?H4 ?H5 => is_ind P; destruct' H0; destruct' H1; destruct' H2; destruct' H3; destruct' H4; destruct' H5
  | ?P ?H0 ?H1 ?H2 ?H3 ?H4 => is_ind P; destruct' H0; destruct' H1; destruct' H2; destruct' H3; destruct' H4
  | ?P ?H0 ?H1 ?H2 ?H3 => is_ind P; destruct' H0; destruct' H1; destruct' H2; destruct' H3
  | ?P ?H0 ?H1 ?H2 => is_ind P; destruct' H0; destruct' H1; destruct' H2
  | ?P ?H0 ?H1 => is_ind P; destruct' H0; destruct' H1
  | ?P ?H0 => is_ind P; destruct' H0
  | ?P => is_ind P || is_constructor P || is_const P
  end || fail "don't know what to destruct".

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

Theorem nat_ind3: forall (P: nat -> nat -> nat -> Prop),
    P 0 0 0 ->
    (forall x, P x 0 0 -> P (S x) 0 0) ->
    (forall y, P 0 y 0 -> P 0 (S y) 0) ->
    (forall z, P 0 0 z -> P 0 0 (S z)) ->
    (forall x y, P x y 0 -> P (S x) (S y) 0) ->
    (forall x z, P x 0 z -> P (S x) 0 (S z)) ->
    (forall y z, P 0 y z -> P 0 (S y) (S z)) ->
    (forall x y z, P x y z -> P (S x) (S y) (S z)) ->
    forall x y z, P x y z.
Proof.
  intros P P0 Px Py Pz Pxy Pxz Pyz Pxyz xs.
  induction xs; intros ys; induction ys; intros zs; induction zs.
  - exact P0.
  - apply Pz.
    exact IHzs.
  - apply Py.
    exact (IHys 0).
  - apply Pyz.
    exact (IHys zs).
  - apply Px.
    exact (IHxs 0 0).
  - apply Pxz.
    exact (IHxs 0 zs).
  - apply Pxy.
    exact (IHxs ys 0).
  - apply Pxyz.
    exact (IHxs ys zs).
Qed.

Ltac ind_nat3 x y z :=
  revert x y z;
  match goal with
  | [ |- forall x y z, ?H ] => apply (nat_ind3 (fun x y z => H))
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

Theorem list_ind3: forall {A B C: Type} (P: list A -> list B -> list C -> Prop),
    P nil nil nil ->
    (forall x xs, P xs nil nil -> P (cons x xs) nil nil) ->
    (forall y ys, P nil ys nil -> P nil (cons y ys) nil) ->
    (forall z zs, P nil nil zs -> P nil nil (cons z zs)) ->
    (forall x y xs ys, P xs ys nil -> P (cons x xs) (cons y ys) nil) ->
    (forall x z xs zs, P xs nil zs -> P (cons x xs) nil (cons z zs)) ->
    (forall y z ys zs, P nil ys zs -> P nil (cons y ys) (cons z zs)) ->
    (forall x y z xs ys zs, P xs ys zs -> P (cons x xs) (cons y ys) (cons z zs)) ->
    forall xs ys zs, P xs ys zs.
Proof.
  intros A B C P P0 Px Py Pz Pxy Pxz Pyz Pxyz xs.
  induction xs; intros ys; induction ys; intros zs; induction zs.
  - exact P0.
  - apply Pz.
    exact IHzs.
  - apply Py.
    exact (IHys nil).
  - apply Pyz.
    exact (IHys zs).
  - apply Px.
    exact (IHxs nil nil).
  - apply Pxz.
    exact (IHxs nil zs).
  - apply Pxy.
    exact (IHxs ys nil).
  - apply Pxyz.
    exact (IHxs ys zs).
Qed.

Ltac ind_list3 x y z :=
  revert x y z;
  match goal with
  | [ |- forall x y z, ?H ] => apply (list_ind3 (fun x y z => H))
  end.

Theorem list_ind2_alt_l: forall {A B: Type} (P: list A -> list B -> Prop),
    P nil nil ->
    (forall x xs, P xs nil -> P (cons x xs) nil) ->
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

Ltac ind_list2_alt_l x y :=
  revert x y;
  match goal with
  | [ |- forall x y, ?H ] => apply (list_ind2_alt_l (fun x y => H))
  end.

Theorem list_ind2_alt_r: forall {A B: Type} (P: list A -> list B -> Prop),
    P nil nil ->
    (forall x xs ys, P xs ys -> P (cons x xs) ys) ->
    (forall y ys, P nil ys -> P nil (cons y ys)) ->
    forall xs ys, P xs ys.
Proof.
  intros A B P P0 Px Py xs ys.
  apply (@list_ind2_alt_l B A (fun b a => P a b)); intros.
  - apply P0.
  - apply Py; exact H.
  - apply Px; exact H.
Qed.

Ltac ind_list2_alt_r x y :=
  revert x y;
  match goal with
  | [ |- forall x y, ?H ] => apply (list_ind2_alt_r (fun x y => H))
  end.

Lemma list_add_ind : forall {A: Type} (P: list A -> Prop),
    P nil ->
    (forall xs xs', P xs -> (exists x, List.Add x xs xs') -> P xs') ->
    forall xs, P xs.
Proof.
  intros A P P0 Pn xs; induction xs; [exact P0 | apply (Pn xs); [exact IHxs |]]. exists a. apply List.Add_head.
Qed.

Tactic Notation "induction2" ident(a) ident(b) "using" tactic(ind2) :=
  revert_with a; revert_with b; ind2 a b; intros.

Tactic Notation "induction3" ident(a) ident(b) ident(c) "using" tactic(ind3) :=
  revert_with a; revert_with b; revert_with c; ind3 a b c; intros.
