(* Add LoadPath should not be necessary but it is *)
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.
From NS Require Import Misc.
From NS Require Import JsRecord.
From NS Require Import TypesBase.
From NS Require Import TypesNotation.

Definition map_itype {A B: Set} (f: A -> B) (a: itype A): itype B :=
match a with
| It name targs => It name (List.map f targs)
end.

Definition map_vtype {A B: Set} (f: A -> B) (a: vtype A): vtype B :=
match a with
| VVoid => VVoid
| Vt a => Vt (f a)
end.

Definition map_tparam {A B: Set} (f: A -> B) (a: tparam A): tparam B :=
match a with
| TParam v name supers => TParam v name (List.map f supers)
end.

Definition map_otype {A B: Set} (f: A -> B) (a: otype A): otype B :=
match a with
| Ot nullable a => Ot nullable (f a)
end.

Definition map_stype {A B: Set} (f: A -> B) (a: stype A): stype B :=
match a with
| SFn tparams thisp params rparam ret => SFn (List.map (map_tparam f) tparams) (f thisp) (List.map (map_otype f) params) (f rparam) (map_vtype f ret)
| SArray elem => SArray (f elem)
| STuple elems => STuple (List.map (map_otype f) elems)
| SObject fields => SObject (map_js_record (map_otype f) fields)
end.

Fixpoint thinnify (a: ftype): ttype :=
match a with
| FAny => TAny
| FNever nullable => TNever nullable
| FStructural nullable s => TStructural nullable (map_stype thinnify s)
| FNominal nullable id _ _ => TNominal nullable (map_itype thinnify id)
end.

Definition is_ttype_nullable (a: ttype): bool :=
match a with
| TAny => true
| TNever nullable => nullable
| TStructural nullable _ => nullable
| TNominal nullable _ => nullable
end.

Definition is_nullable (a: ftype): bool :=
match a with
| FAny => true
| FNever nullable => nullable
| FStructural nullable _ => nullable
| FNominal nullable _ _ _ => nullable
end.

Definition IsNullable (a: ftype): Prop :=
match a with
| FAny => True
| FNever nullable => Bool.Is_true nullable
| FStructural nullable _ => Bool.Is_true nullable
| FNominal nullable _ _ _ => Bool.Is_true nullable
end.

Definition ttype_add_null_if (cond: bool) (a: ttype): ttype :=
match a with
| TAny => TAny
| TNever nullable => TNever (cond || nullable)
| TStructural nullable s => TStructural (cond || nullable) s
| TNominal nullable id => TNominal (cond || nullable) id
end.

Definition add_null_if (cond: bool) (a: ftype): ftype :=
match a with
| FAny => FAny
| FNever nullable => FNever (cond || nullable)
| FStructural nullable s => FStructural (cond || nullable) s
| FNominal nullable id sids s => FNominal (cond || nullable) id sids s
end.

Definition ttype_collapse_opt (nullable: bool) (a: option ttype): ttype :=
match a with
| None => TAny
| Some a => a
end.

Definition collapse_opt (nullable: bool) (a: option ftype): ftype :=
match a with
| None => FAny
| Some a => a
end.

Definition itype_id {type: Set} (a: itype type): string :=
match a with
| It name _ => name
end.

Definition itype_targs {type: Set} (a: itype type): list type :=
match a with
| It _ targs => targs
end.

Definition vtype_depth {type: Set} (type_depth: type -> nat) (a: vtype type): nat :=
match a with
| VVoid => 0
| Vt a => type_depth a
end.

Definition vtype_size {type: Set} (type_size: type -> nat) (a: vtype type): nat :=
match a with
| VVoid => 0
| Vt a => type_size a
end.

Definition otype_depth {type: Set} (type_depth: type -> nat) (a: otype type): nat :=
match a with
| Ot _ a => type_depth a
end.

Definition otype_size {type: Set} (type_size: type -> nat) (a: otype type): nat :=
match a with
| Ot _ a => type_size a
end.

Definition tparam_depth {type: Set} (type_depth: type -> nat) (a: tparam type): nat :=
match a with
| TParam _ _ supers => List.list_max (List.map type_depth supers)
end.

Definition tparam_size {type: Set} (type_size: type -> nat) (a: tparam type): nat :=
match a with
| TParam _ _ supers => List.list_sum (List.map type_size supers)
end.

Definition itype_depth {type: Set} (type_depth: type -> nat) (a: itype type): nat :=
match a with
| It _ targs => List.list_max (List.map type_depth targs)
end.

Definition itype_size {type: Set} (type_size: type -> nat) (a: itype type): nat :=
match a with
| It _ targs => List.list_sum (List.map type_size targs)
end.

Definition stype_depth {type: Set} (type_depth: type -> nat) (a: stype type): nat :=
match a with
| SFn tparams thisp params rparam ret => List.list_max (
    type_depth thisp ::
    type_depth rparam ::
    vtype_depth type_depth ret ::
    List.map (tparam_depth type_depth) tparams ++
    List.map (otype_depth type_depth) params)%list
| SArray elem => type_depth elem
| STuple elems => List.list_max (List.map (otype_depth type_depth) elems)
| SObject fields => List.list_max (List.map (otype_depth type_depth << snd) fields)
end.

Definition stype_size {type: Set} (type_size: type -> nat) (a: stype type): nat :=
match a with
| SFn tparams thisp params rparam ret => List.list_sum (
    type_size thisp ::
    type_size rparam ::
    vtype_size type_size ret ::
    List.map (tparam_size type_size) tparams ++
    List.map (otype_size type_size) params)%list
| SArray elem => type_size elem
| STuple elems => List.list_sum (List.map (otype_size type_size) elems)
| SObject fields => List.list_sum (List.map (otype_size type_size << snd) fields)
end.

Fixpoint ttype_depth (a: ttype): nat := S (
match a with
| TAny => 0
| TNever _ => 0
| TStructural _ s => stype_depth ttype_depth s
| TNominal _ id => itype_depth ttype_depth id
end).

Fixpoint ttype_size (a: ttype): nat := S (
match a with
| TAny => 0
| TNever _ => 0
| TStructural _ s => stype_size ttype_size s
| TNominal _ id => itype_size ttype_size id
end).

Fixpoint ftype_depth (a: ftype): nat := S (
match a with
| FAny => 0
| FNever _ => 0
| FStructural _ s => stype_depth ftype_depth s
| FNominal _ id sids s => Nat.max (itype_depth ftype_depth id) (Nat.max (List.list_max (List.map (itype_depth ftype_depth) sids)) (option_max (option_map (stype_depth ftype_depth) s)))
end).

Fixpoint ftype_size (a: ftype): nat := S (
match a with
| FAny => 0
| FNever _ => 0
| FStructural _ s => stype_size ftype_size s
| FNominal _ id sids s => List.list_sum (itype_size ftype_size id :: option_map (stype_size ftype_size) s ?:: List.map (itype_size ftype_size) sids)
end).

Notation ftype' nat := {x: ftype | ftype_depth x <= nat}.
Program Axiom ftype_ind_depth:
  forall (P: forall (n: nat), ftype' n -> Prop)
    (pAny: P 1 FAny)
    (pNever: forall (nullable: bool), P 1 (FNever nullable))
    (pStructural: forall (n: nat) (IHn: forall (a: ftype' n), P n a) (nullable: bool) (s: stype (ftype' n)), P (S n) (FStructural nullable s))
    (pNominal: forall (n: nat) (IHn: forall (a: ftype' n), P n a) (nullable: bool) (id: itype (ftype' n)) (sids: list (itype (ftype' n))) (s: option (stype (ftype' n))), P (S n) (FNominal nullable id sids s))
    (a: ftype),
    P a.



Definition option_conv {A: Set} {B: nat -> Set} (df: A -> nat) (f: forall (a0: A), B (df a0)) (a: option A): option' B (option_max (option_map df a)) :=
match a with | Some a => Some' (f a) | None => None' end.
Definition option'_conv {A: nat -> Set} {B: Set} {n: nat} (f: A n -> B) (a: option' A n): option B.
destruct a; [apply Some; apply f; exact a | apply None]. Defined.
Fixpoint list_conv {A: Set} {B: nat -> Set} (df: A -> nat) (f: forall (a0: A), B (df a0)) (a: list A): list' B (List.list_max (List.map df a)) :=
match a with | nil => Nil' | cons a a0 => Cons' (f a) (list_conv df f a0) end.
Definition list'_conv {A: nat -> Set} {B: Set} {n: nat} (f: forall n0, n0 <= n -> A n0 -> B) (a: list' A n): list B.
induction a; [apply nil | apply cons; [apply f with n; [apply Nat.le_max_l | exact a] | apply IHa; intros; apply f with n1; [eapply Nat.le_trans; [exact H | apply Nat.le_max_r] | exact H0]]]. Defined.
Local Obligation Tactic := lia || intuition.
Program Fixpoint ftype'_conv {n: nat} (t: ftype' n) {measure n}: ftype :=
  match t with
  | FAny' => FAny
  | FNever' nullable => FNever nullable
  | FStructural' nullable structure => FStructural nullable (map_stype (fun a => ftype'_conv a) structure)
  | FNominal' nullable id sids structure => FNominal nullable (map_itype (fun a => ftype'_conv a) id) (list'_conv (fun n prf => map_itype (fun a => ftype'_conv a)) sids) (option'_conv (map_stype (fun a => ftype'_conv a)) structure)
  end.
(* Program Fixpoint ftype_conv {n: nat} (t: {t: ftype | ftype_depth t = n}) {measure n}: ftype' n :=
match t with
| FAny => FAny'
| FNever nullable => FNever' nullable
| FStructural nullable structure => @FStructural' _ nullable (map_stype (fun a => ftype_conv _) structure)
| FNominal nullable id sids structure => @FNominal' _ _ _ nullable (map_itype (fun a => ftype_conv _) id) (list_conv (itype_depth (fun a => ftype_depth a)) (fun a0 => map_itype (fun a => ftype_conv _) a0) sids) (option_conv (stype_depth (fun a => ftype_depth a)) (fun a0 => map_stype (fun a => ftype_conv _) a0) structure)
end. *)
Local Ltac rewrite_admit a b := let H := fresh "H" in assert (H: a = b); [admit |]; rewrite H; clear H.
Definition ftype_conv (t: ftype): ftype' (ftype_depth t).
remember (ftype_depth t) as n; revert Heqn; revert t; induction n; intros; [destruct t; discriminate Heqn |].
destruct t; simpl in Heqn; rewrite Heqn; [apply FAny' | apply FNever'; exact nullable | |].
- apply FStructural'; [exact nullable | eapply map_stype; [intros H | exact structure]]; inv Heqn; apply IHn with H; admit.
- apply FNominal'; [exact nullable | eapply map_itype; [intros H | exact id] | apply list_conv; intros H | apply option_conv; intros H ]; [| eapply map_itype; [rename H into H0; intros H | exact H] | eapply map_stype; [rename H into H0; intros H | exact H]]; [rewrite_admit (itype_depth ftype_depth id) n | rewrite_admit (itype_depth ftype_depth H0) n | rewrite_admit (stype_depth ftype_depth H0) n]; apply IHn with H; admit.
Admitted.
