(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
From NS Require Import Misc.

Lemma forall_cons_opt: forall {A: Type} (P: A -> Prop) (x : option A) (xs : list A),
  Option_Forall P x /\ List.Forall P xs <-> List.Forall P (cons_opt x xs).
Proof.
  intros A P x xs.
  split.
  - intros [P0 P1].
    destruct x; simpl.
    + inv P0.
      apply List.Forall_cons; [exact H1 | exact P1].
    + exact P1.
  - intros H.
    destruct x; simpl in H.
    + inv H.
      split; [apply Option_Forall_Some; exact H2 | exact H3].
    + split; [apply Option_Forall_None | exact H].
Qed.

Lemma non_empty_cons_opt: forall {A: Type} (x : option A) (xs : list A),
  x <> None \/ xs <> nil <-> cons_opt x xs <> nil.
Proof.
  intros A x xs.
  split.
  - intros [P | P].
    + destruct x; [| contradiction P; reflexivity].
      simpl. discriminate.
    + destruct x; simpl; [discriminate | exact P].
  - destruct x; simpl.
    + intros _. left. discriminate.
    + intros H. right. exact H.
Qed.

Lemma forall_find_map: forall {A B: Type} (P: B -> Prop) (f g: A -> option B),
 (forall a, g a = None -> f a = None) ->
 (forall a, (forall a, g a = None -> f a = None) -> Option_Forall P (f a) -> Option_Forall P (g a)) ->
 forall (xs: list A), Option_Forall P (find_map f xs) -> Option_Forall P (find_map g xs).
Proof.
  intros A B P f g H0 H1 xs.
  induction xs; simpl; intros H2; [apply Option_Forall_None |].
  destruct (g a) eqn:gaeq.
  - specialize (H1 a).
    rewrite gaeq in H1.
    apply H1; [exact H0 |].
    destruct (f a).
    + exact H2.
    + apply Option_Forall_None.
  - apply IHxs.
    destruct (f a) eqn:faeq.
    + specialize (H0 a gaeq). rewrite H0 in faeq. discriminate faeq.
    + exact H2.
Qed.

(* Literally the exact same proof, but I'm too lazy to abstract and doesn't really affect anything due to proof irrelevance *)
Lemma forall_find_map': forall {A B0 B1: Type} (P0: B0 -> Prop) (P1: B1 -> Prop) (f: A -> option B0) (g: A -> option B1),
 (forall a, g a = None -> f a = None) ->
 (forall a, (forall a, g a = None -> f a = None) -> Option_Forall P0 (f a) -> Option_Forall P1 (g a)) ->
 forall (xs: list A), Option_Forall P0 (find_map f xs) -> Option_Forall P1 (find_map g xs).
Proof.
  intros A B0 B1 P0 P1 f g H0 H1 xs.
  induction xs; simpl; intros H2; [apply Option_Forall_None |].
  destruct (g a) eqn:gaeq.
  - specialize (H1 a).
    rewrite gaeq in H1.
    apply H1; [exact H0 |].
    destruct (f a).
    + exact H2.
    + apply Option_Forall_None.
  - apply IHxs.
    destruct (f a) eqn:faeq.
    + specialize (H0 a gaeq). rewrite H0 in faeq. discriminate faeq.
    + exact H2.
Qed.

Lemma non_empty_find_map: forall {A B: Type} (f g: A -> option B),
 (forall a, g a = None -> f a = None) ->
 forall (xs: list A), find_map f xs <> None -> find_map g xs <> None.
Proof.
  intros A B f g H xs.
  induction xs; simpl; intros H0; [exact H0 |].
  destruct (g a) eqn:gaeq; [discriminate |].
  apply IHxs.
  destruct (f a) eqn: faeq.
  - specialize (H a gaeq). rewrite H in faeq. discriminate faeq.
  - exact H0.
Qed.

Lemma forall_option_map: forall {A B: Type} (P: B -> Prop) (f g: A -> B),
 (forall a, P (f a) -> P (g a)) ->
 forall (a: option A), Option_Forall P (option_map f a) -> Option_Forall P (option_map g a).
Proof.
  intros A B P f g H a.
  destruct a; simpl; intros H0; [| apply Option_Forall_None].
  apply Option_Forall_Some. inv H0. exact (H a H3).
Qed.

Lemma forall_option_map': forall {A B0 B1: Type} (P0: B0 -> Prop) (P1: B1 -> Prop) (f: A -> B0) (g: A -> B1),
 (forall a, P0 (f a) -> P1 (g a)) ->
 forall (a: option A), Option_Forall P0 (option_map f a) -> Option_Forall P1 (option_map g a).
Proof.
  intros A B0 B1 P0 P1 f g H a.
  destruct a; simpl; intros H0; [| apply Option_Forall_None].
  apply Option_Forall_Some. inv H0. exact (H a H3).
Qed.

Lemma forall_intersect: forall {A B C: Type} (P: C -> Prop) (f g: A -> B -> option C),
 (forall a b, g a b = None -> f a b = None) ->
 (forall a b, (forall a b, g a b = None -> f a b = None) -> Option_Forall P (f a b) -> Option_Forall P (g a b)) ->
 forall (xs: list A) (ys: list B), List.Forall P (intersect f xs ys) -> List.Forall P (intersect g xs ys).
Proof.
  intros A B C P f g H0 H1 xs.
  induction xs; simpl; intros ys H2; [apply List.Forall_nil |].
  apply forall_cons_opt. rewrite <- forall_cons_opt in H2.
  split; [destruct H2 as [H2 _] | destruct H2 as [_ H2]].
  - apply (forall_find_map (f a) (g a)).
    + apply H0.
    + intros b H. apply H1. apply H0.
    + exact H2.
  - exact (IHxs ys H2).
Qed.

Lemma forall_intersect': forall {A B C0 C1: Type} (P0: C0 -> Prop) (P1: C1 -> Prop) (f: A -> B -> option C0) (g: A -> B -> option C1),
 (forall a b, g a b = None -> f a b = None) ->
 (forall a b, (forall a b, g a b = None -> f a b = None) -> Option_Forall P0 (f a b) -> Option_Forall P1 (g a b)) ->
 forall (xs: list A) (ys: list B), List.Forall P0 (intersect f xs ys) -> List.Forall P1 (intersect g xs ys).
Proof.
  intros A B C0 C1 P0 P1 f g H0 H1 xs.
  induction xs; simpl; intros ys H2; [apply List.Forall_nil |].
  apply forall_cons_opt. rewrite <- forall_cons_opt in H2.
  split; [destruct H2 as [H2 _] | destruct H2 as [_ H2]].
  - apply (@forall_find_map' B C0 C1 P0 P1 (f a) (g a)).
    + apply H0.
    + intros b H. apply H1. apply H0.
    + exact H2.
  - exact (IHxs ys H2).
Qed.

Lemma non_empty_intersect: forall {A B C: Type} (f g: A -> B -> option C),
 (forall a b, g a b = None -> f a b = None) ->
 forall (xs: list A) (ys: list B), intersect f xs ys <> nil -> intersect g xs ys <> nil.
Proof.
  intros A B C f g H xs.
  induction xs; simpl; intros ys H0; [exact H0 |].
  apply non_empty_cons_opt. rewrite <- non_empty_cons_opt in H0.
  inv H0; [left | right].
  - apply (non_empty_find_map (f a) (g a)); [exact (H a) | exact H1].
  - exact (IHxs ys H1).
Qed.

Lemma forall_js_record_zip_with: forall {A B C: Set} (P: C -> Prop) (f g: A -> B -> C),
 (forall a b, P (f a b) -> P (g a b)) ->
 forall (xs: js_record A) (ys: js_record B),
   List.Forall (fun z => P (snd z)) (js_record_zip_with f xs ys) ->
   List.Forall (fun z => P (snd z)) (js_record_zip_with g xs ys).
Proof.
  intros A B C P f g H xs.
  induction xs; simpl; intros ys H2; [apply List.Forall_nil |].
  destruct a as [x_key x].
  apply forall_cons_opt. rewrite <- forall_cons_opt in H2.
  split; [destruct H2 as [H2 _] | destruct H2 as [_ H2]].
  - revert H2. apply forall_option_map.
    simpl. exact (H x).
  - apply IHxs. exact H2.
Qed.

Lemma forall_js_record_zip_with': forall {A B C0 C1: Set} (P0: C0 -> Prop) (P1: C1 -> Prop) (f: A -> B -> C0) (g: A -> B -> C1),
 (forall a b, P0 (f a b) -> P1 (g a b)) ->
 forall (xs: js_record A) (ys: js_record B),
   List.Forall (fun z => P0 (snd z)) (js_record_zip_with f xs ys) ->
   List.Forall (fun z => P1 (snd z)) (js_record_zip_with g xs ys).
Proof.
  intros A B C0 C1 P0 P1 f g H xs.
  induction xs; simpl; intros ys H2; [apply List.Forall_nil |].
  destruct a as [x_key x].
  apply forall_cons_opt. rewrite <- forall_cons_opt in H2.
  split; [destruct H2 as [H2 _] | destruct H2 as [_ H2]].
  - revert H2. apply forall_option_map'.
    simpl. exact (H x).
  - apply IHxs. exact H2.
Qed.

Lemma forall_zip_with: forall {A B C: Type} (P: C -> Prop) (f g: A -> B -> C),
 (forall a b, P (f a b) -> P (g a b)) ->
 forall (xs: list A) (ys: list B), List.Forall P (zip_with f xs ys) -> List.Forall P (zip_with g xs ys).
Proof.
  intros A B C P f g H xs ys.
  ind_list2 xs ys; simpl; try (intros; apply List.Forall_nil).
  intros x y xs ys IH H0.
  inv H0.
  apply List.Forall_cons; [clear H4 | clear H3].
  - exact (H x y H3).
  - exact (IH H4).
Qed.

Lemma forall_zip_with': forall {A B C0 C1: Type} (P0: C0 -> Prop) (P1: C1 -> Prop) (f: A -> B -> C0) (g: A -> B -> C1),
 (forall a b, P0 (f a b) -> P1 (g a b)) ->
 forall (xs: list A) (ys: list B), List.Forall P0 (zip_with f xs ys) -> List.Forall P1 (zip_with g xs ys).
Proof.
  intros A B C0 C1 P0 P1 f g H xs ys.
  ind_list2 xs ys; simpl; try (intros; apply List.Forall_nil).
  intros x y xs ys IH H0.
  inv H0.
  apply List.Forall_cons; [clear H4 | clear H3].
  - exact (H x y H3).
  - exact (IH H4).
Qed.

Lemma forall_option_zip_with: forall {A B C: Type} (P: C -> Prop) (f g: A -> B -> C),
 (forall a b, P (f a b) -> P (g a b)) ->
 forall (a: option A) (b: option B), Option_Forall P (option_zip_with f a b) -> Option_Forall P (option_zip_with g a b).
Proof.
  intros A B C P f g H a b.
  destruct a; destruct b; simpl; try (intros; apply Option_Forall_None).
  intros H0.
  inv H0.
  apply Option_Forall_Some.
  exact (H a b H3).
Qed.

Lemma forall_option_zip_with': forall {A B C0 C1: Type} (P0: C0 -> Prop) (P1: C1 -> Prop) (f0: A -> B -> C0) (f1: A -> B -> C1),
 (forall a b, P0 (f0 a b) -> P1 (f1 a b)) ->
 forall (a: option A) (b: option B), Option_Forall P0 (option_zip_with f0 a b) -> Option_Forall P1 (option_zip_with f1 a b).
Proof.
  intros A B C0 C1 P0 P1 f0 f1 H a b.
  destruct a; destruct b; simpl; try (intros; apply Option_Forall_None).
  intros H0.
  inv H0.
  apply Option_Forall_Some.
  exact (H a b H3).
Qed.

Lemma zip_with_nil: forall {A B C: Type} (f : A -> B -> C) (xs : list A), @zip_with A B C f xs nil = nil.
Proof.
  intros A B C f xs.
  destruct xs; reflexivity.
Qed.

Lemma intersect_nil: forall {A B C: Type} (f : A -> B -> option C) (xs : list A), @intersect A B C f xs nil = nil.
Proof.
  intros A B C f xs.
  induction xs; simpl; [reflexivity |].
  exact IHxs.
Qed.

Lemma cons_opt_nil: forall {A: Type} (x: option A) (xs: list A), cons_opt x xs = nil <-> x = None /\ xs = nil.
Proof.
  intros A x.
  induction xs; destruct x; split; simpl;
    try discriminate;
    try (intros [H0 H1]; discriminate H0 || discriminate H1);
    try reflexivity;
    try (split; reflexivity).
Qed.

Lemma forall_intersect_cons_r: forall {A B C: Type} (P: C -> Prop) (f: A -> B -> option C) (xs: list A) (y: B),
 List.Forall P (filter_map (fun x => f x y) xs) ->
 forall (ys: list B), List.Forall P (intersect f xs ys) -> List.Forall P (intersect f xs (cons y ys)).
Proof.
  intros A B C P f xs y H.
  induction xs; simpl; [intros; apply List.Forall_nil |].
  rename a into x.
  destruct (f x y) eqn:feq; intros ys H1;
    rewrite <- forall_cons_opt in H1;
    apply forall_cons_opt;
    destruct H1 as [H1 H2];
    simpl in H; rewrite feq in H; simpl in H; inv H;
    split.
  - apply Option_Forall_Some; exact H4.
  - apply IHxs; [exact H5 | exact H2].
  - exact H1.
  - apply IHxs; [rewrite <- H3; apply List.Forall_nil | exact H2].
  - exact H1.
  - apply IHxs; [rewrite <- H0; apply List.Forall_cons | exact H2].
    + exact H3.
    + exact H4.
Qed.

Inductive Cartesian_Forall {A B C: Type} (P: C -> Prop) (f: A -> B -> C): list A -> list B -> Prop :=
| Cartesian_Forall_nil: forall (ys: list B), Cartesian_Forall P f nil ys
| Cartesian_Forall_cons: forall (x: A) (xs: list A) (ys: list B),
   List.Forall (fun y => P (f x y)) ys -> Cartesian_Forall P f xs ys -> Cartesian_Forall P f (cons x xs) ys.
