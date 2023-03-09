(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
From NS Require Import Misc.

Theorem list_max_map0: forall {A: Type} (a: list A), list_max (List.map (fun _ => 0) a) = 0.
Proof.
  induction 0; simpl; [reflexivity | exact IHa].
Qed.

Theorem option_max_map0: forall {A: Type} (a: option A), option_max (option_map (fun _ => 0) a) = 0.
Proof.
  destruct 0; by_ simpl.
Qed.

Theorem list_max_cons_le: forall (y: nat) (x: nat) (xs: list nat), list_max (x :: xs) <= y <-> x <= y /\ list_max xs <= y.
Proof.
  split; intros H.
  - simpl in H. rewrite <- Nat.max_lub_iff. exact H.
  - simpl. rewrite Nat.max_lub_iff. exact H.
Qed.

Theorem list_max_cons_opt_le: forall (y: nat) (x: option nat) (xs: list nat), list_max (x ?:: xs) <= y <-> option_max x <= y /\ list_max xs <= y.
Proof.
  split; destruct x; simpl; intros H.
  - simpl in H. rewrite <- Nat.max_lub_iff. exact H.
  - split; [apply Nat.le_0_l | exact H].
  - simpl. rewrite Nat.max_lub_iff. exact H.
  - destruct H as [_ H]. exact H.
Qed.

Theorem list_max_cons_lt: forall (y: nat) (x: nat) (xs: list nat), list_max (x :: xs) < y <-> x < y /\ list_max xs < y.
Proof.
  split; intros H.
  - simpl in H. rewrite <- Nat.max_lub_lt_iff. exact H.
  - simpl. rewrite Nat.max_lub_lt_iff. exact H.
Qed.

Theorem list_max_cons_opt_lt: forall (y: nat) (x: option nat) (xs: list nat), list_max (x ?:: xs) < S y <-> option_max x < S y /\ list_max xs < S y.
Proof.
  split; destruct x; simpl; intros H.
  - simpl in H. rewrite <- Nat.max_lub_lt_iff. exact H.
  - split; [apply Nat.lt_0_succ | exact H].
  - simpl. rewrite Nat.max_lub_lt_iff. exact H.
  - destruct H as [_ H]. exact H.
Qed.

Theorem list_max_all_le: forall (b: nat) (xs: list nat), List.Forall (fun a => a <= b) xs -> list_max xs <= b.
Proof.
  intros b xs.
  induction xs; simpl.
  - intros _. apply Nat.le_0_l.
  - intros H. inv H. specialize (IHxs H3). rewrite Nat.max_lub_iff. split; [exact H2 | exact IHxs].
Qed.

Theorem option_max_all_le: forall (b: nat) (xs: option nat), Option_Forall (fun a => a <= b) xs -> option_max xs <= b.
Proof.
  intros b xs.
  destruct xs; simpl.
  - intros H. inv H. exact H2.
  - intros _. apply Nat.le_0_l.
Qed.

Theorem list_max_map_all_le: forall {A: Type} (f: A -> nat) (b: nat) (xs: list A),
    List.Forall (fun a => f a <= b) xs -> list_max (List.map f xs) <= b.
Proof.
  intros A f b xs H.
  apply list_max_all_le.
  rewrite List.Forall_map.
  exact H.
Qed.

Lemma option_forall_map: forall {A B : Type} (f : A -> B) (P : B -> Prop) (a : option A),
    Option_Forall P (option_map f a) <-> Option_Forall (fun x : A => P (f x)) a.
Proof.
  intros A B f P a.
  split; intros H; destruct a.
  2, 4: apply Option_Forall_None.
  1, 2: apply Option_Forall_Some; simpl in H; inv H; exact H2.
Qed.

Theorem option_max_map_all_le: forall {A: Type} (f: A -> nat) (b: nat) (xs: option A),
    Option_Forall (fun a => f a <= b) xs -> option_max (option_map f xs) <= b.
Proof.
  intros A f b xs H.
  apply option_max_all_le.
  rewrite option_forall_map.
  exact H.
Qed.

Theorem list_forall_weaken: forall {A: Type} (P: A -> Prop), (forall a, P a) -> forall (xs: list A), List.Forall P xs.
Proof.
  intros A P H xs.
  induction xs; [apply List.Forall_nil | apply List.Forall_cons].
  - exact (H a).
  - exact IHxs.
Qed.

Theorem option_forall_weaken: forall {A: Type} (P: A -> Prop), (forall a, P a) -> forall (xs: option A), Option_Forall P xs.
Proof.
  intros A P H xs.
  destruct xs; [apply Option_Forall_Some | apply Option_Forall_None].
  - exact (H a).
Qed.

Corollary list_max_map_all_le': forall {A: Type} (f: A -> nat) (b: nat),
    (forall a, f a <= b) -> forall (xs: list A), list_max (List.map f xs) <= b.
Proof.
  intros A f b H xs.
  apply list_max_map_all_le.
  apply list_forall_weaken.
  exact H.
Qed.

Corollary option_max_map_all_le': forall {A: Type} (f: A -> nat) (b: nat),
    (forall a, f a <= b) -> forall (xs: option A), option_max (option_map f xs) <= b.
Proof.
  intros A f b H xs.
  apply option_max_map_all_le.
  apply option_forall_weaken.
  exact H.
Qed.
