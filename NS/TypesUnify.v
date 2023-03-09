(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Add LoadPath "tlc/src" as TLC.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import FunInd.
From NS Require Import Misc.
From NS Require Import TypesBase.
From NS Require Import TypesSimpleHelpers.
From NS Require Import TypesInduction.

Inductive sj_fn_loc: Set :=
| InParam (idx: nat)
| InRestParam
| InReturn.

Inductive sj_loc: Set :=
| InGeneric (a: string) (idx: nat)
| InFn (a: sj_fn_loc)
| InArray
| InTuple (idx: nat)
| InObject (field: string).

Inductive sj_fn_struct_err: Set :=
| DifferentTParams
| DifferentNumParams
| DifferentHasRestParam
| DifferentVoidReturn.

Inductive sj_struct_err: Set :=
| DifferentStructKinds
| DifferentFn (a: sj_fn_struct_err)
| DifferentNumElems
| DifferentFields.

Inductive sj_err: Set :=
| MissingAny
| Nullable
| MissingNominal (a: string)
| MissingNever
| Structural (a: sj_struct_err)
| InLoc (loc: sj_loc) (inner: sj_err).

(* Subtype judgement *)
Definition sj: Set := list sj_err.

(* Unify + subtype judgement *)
Inductive uj (type: Set): Set :=
| UJ (union: type) (s: sj).
Arguments UJ {type}.

Definition uj0 {type: Set} (a: type): uj type := UJ a nil.
Definition uj_cons {type: Set} (err: sj_err) (a: uj type) :=
match a with
| UJ union s => UJ union (cons err s)
end.
Definition uj1 {type: Set} (err: sj_err) (a: type): uj type := uj_cons err (uj0 a).
Definition uj_cons_iff {type: Set} (err: sj_err) (cond: bool) (a: uj type) :=
if cond then uj_cons err a else a.
Definition uj_cons_map {type A: Set} (err: A -> sj_err) (cond: option A) (a: uj type) :=
match cond with
| None => a
| Some cond => uj_cons (err cond) a
end.

Definition loc_uj_errs {A: Set} (loc: sj_loc) (a: uj A): uj A :=
match a with
| UJ union s => UJ union (List.map (InLoc loc) s)
end.

(* uj is a monad (writer) *)
Definition map_uj {A B: Set} (f: A -> B) (a: uj A): uj B :=
match a with
| UJ union s => UJ (f union) s
end.

Definition ap_uj {A B: Set} (f: uj (A -> B)) (a: uj A): uj B :=
match f, a with
| UJ f sf, UJ a sa => UJ (f a) (app sf sa)
end.

Definition then_uj {A B: Set} (f: A -> uj B) (a: uj A): uj B :=
match a with
| UJ union s =>
    match f union with
    | UJ union s' => UJ union (app s' s)
    end
end.

Notation "f '<uj$>' x" := (map_uj f x) (at level 84, left associativity).
Notation "f '<uj*>' x" := (ap_uj f x) (at level 84, left associativity).
Notation "f '=uj<<' x" := (then_uj f x) (at level 84, left associativity).

Fixpoint traverse_uj {A: Set} (xs: list (uj A)): uj (list A) :=
match xs with
| nil => uj0 nil
| cons x xs => cons <uj$> x <uj*> traverse_uj xs
end.

Fixpoint _traverse_loc_uj {A: Set} (loc: nat -> sj_loc) (idx: nat) (xs: list (uj A)): uj (list A) :=
match xs with
| nil => uj0 nil
| cons x xs => cons <uj$> loc_uj_errs (loc idx) x <uj*> _traverse_loc_uj loc (S idx) xs
end.

Definition traverse_loc_uj {A: Set} (loc: nat -> sj_loc): list (uj A) -> uj (list A) := _traverse_loc_uj loc 0.

Fixpoint traverse_loc_uj_fields {A: Set} (loc: string -> sj_loc) (a: js_record (uj A)): uj (js_record A) :=
match a with
| nil => uj0 nil
| cons (x_key, x) xs => cons <uj$> loc_uj_errs (loc x_key) ((fun x => (x_key, x)) <uj$> x) <uj*> traverse_loc_uj_fields loc xs
end.

Definition transpose_option_uj {A: Set} (a: option (uj A)): uj (option A) :=
match a with
| None => uj0 None
| Some uj => Some <uj$> uj
end.

Fixpoint is_sj_err_rt_ok (a: sj_err): bool :=
match a with
| MissingAny => true
| Nullable => true
| MissingNominal _ => true
| MissingNever => false
| Structural _ => false
| InLoc _ inner => is_sj_err_rt_ok inner
end.

Definition is_sj_ok: sj -> bool := is_empty.
Definition is_sj_rt_ok: sj -> bool := all is_sj_err_rt_ok.

Definition itype_id_eqb {type: Set} (a: itype type) (b: itype type): bool :=
match a, b with
| IType a_ident _, IType b_ident _ => String.eqb a_ident b_ident
end.

Definition uj_ftype_join (ids: list (uj (itype ftype))) (s: option (uj (option (stype ftype)) * stype ftype)): uj (option ftype') :=
match ids, s with
| nil, None => uj0 None
| nil, Some (s, _) => option_map FTypeStructural <uj$> s
(* use snd s because we ignore struct errors if unifying into a nominal type (though there shouldn't be any unless there are also nominal errors) *)
| cons id ids, s => map_uj Some <| FTypeNominal <uj$> id <uj*> traverse_uj ids <uj*> uj0 (option_map snd s)
end.

Definition unify_atype {type: Set} (unify: ntype type -> ntype type -> uj (ntype type))
  (asn: atype type) (req: atype type): uj (atype type) :=
match asn, req with
| _, AAny => uj0 AAny
| AAny, _ => uj1 MissingAny AAny
| AType asn_nullable asn, AType req_nullable req =>
    uj_cons_iff Nullable (asn_nullable && negb req_nullable) <|
    map_uj (AType (asn_nullable || req_nullable)) <|
    unify asn req
end.

Definition unify_ntype {type: Set} (unify: type -> type -> uj type)
  (asn: ntype type) (req: ntype type): uj (ntype type) :=
match asn, req with
| NNever, req => uj0 req
| NType asn, NNever => uj1 MissingNever (NType asn)
| NType asn, NType req => NType <uj$> unify asn req
end.

Definition unify_itype {type: Set} (unify: atype type -> atype type -> uj (atype type))
  (asn: itype (atype type)) (req: itype (atype type)): option (uj (itype (atype type))) :=
match asn, req with
| IType asn_ident asn_args, IType req_ident req_args =>
    if negb (String.eqb asn_ident req_ident) then None else
    Some (IType asn_ident <uj$> traverse_loc_uj (InGeneric asn_ident) (zip_with unify asn_args req_args))
end.

Definition unify_vtype {type: Set} (unify: atype type -> atype type -> uj (atype type))
  (asn: vtype (atype type)) (req: vtype (atype type)): uj (vtype (atype type)) :=
match asn, req with
| VVoid, VVoid => uj0 VVoid
| VType asn, VType req => VType <uj$> unify asn req
| _, _ => uj1 (Structural (DifferentFn DifferentVoidReturn)) VVoid
end.

Definition unify_stype {type: Set} (unify: atype type -> atype type -> uj (atype type))
  (asn: stype (atype type)) (req: stype (atype type)): uj (option (stype (atype type))) :=
match asn, req with
| SFn asn_tparams asn_params asn_rparam asn_ret, SFn req_tparams req_params req_rparam req_ret =>
    uj_cons_iff (Structural (DifferentFn DifferentTParams)) (negb (zip_eqb String.eqb asn_tparams req_tparams)) <|
    uj_cons_iff (Structural (DifferentFn DifferentNumParams)) (negb (len asn_params =? len req_params)) <|
    uj_cons_iff (Structural (DifferentFn DifferentHasRestParam)) (negb (Bool.eqb (is_some asn_rparam) (is_some req_rparam))) <|
    map_uj Some <|
      SFn asn_tparams <uj$>
      traverse_loc_uj (InFn << InParam) (zip_with unify req_params asn_params) <uj*>
      loc_uj_errs (InFn InRestParam) (transpose_option_uj (option_zip_with unify req_rparam asn_rparam)) <uj*>
      unify_vtype unify asn_ret req_ret
| SArray asn_elem, SArray req_elem =>
    map_uj Some <| SArray <uj$> loc_uj_errs InArray (unify asn_elem req_elem)
| STuple asn_elems, STuple req_elems =>
    uj_cons_iff (Structural DifferentNumElems) (negb (len asn_elems =? len req_elems)) <|
    map_uj Some <| STuple <uj$> traverse_loc_uj InTuple (zip_with unify asn_elems req_elems)
| SObject asn_fields, SObject req_fields =>
    uj_cons_iff (Structural DifferentFields) (negb (js_record_fields_eqb asn_fields req_fields)) <|
    map_uj Some <| SObject <uj$> traverse_loc_uj_fields InObject (js_record_zip_with unify asn_fields req_fields)
| _, _ => uj1 (Structural DifferentStructKinds) None
end.

Definition unify_stype' {type: Set} (unify: atype type -> atype type -> uj (atype type))
  (asn: option (stype (atype type))) (req: option (stype (atype type))): uj (option (stype (atype type))) :=
match asn, req with
| Some asn, Some req => unify_stype unify asn req
| _, _ => uj0 None
end.

Definition unify_ftype' (unify: ftype -> ftype -> uj ftype) (asn: ftype') (req: ftype'): uj (option ftype') :=
match ftype'_split asn, ftype'_split req with
| (asn_ids, asn_struct), (req_ids, req_struct) =>
    uj_cons_map MissingNominal (option_map itype_id (subtract_hd itype_id_eqb req_ids asn_ids)) <|
      uj_ftype_join
      (intersect (unify_itype unify) asn_ids req_ids)
      (option_zip_with (fun asn_struct req_struct => (unify_stype unify asn_struct req_struct, req_struct)) asn_struct req_struct)
end.

Definition unify_ftype'_alt (unify: ftype -> ftype -> uj ftype) (asn: ftype') (req: ftype'): uj (option ftype') :=
match ftype'_split asn, ftype'_split req with
| (asn_ids, asn_struct), (req_ids, req_struct) =>
    uj_cons_map MissingNominal (option_map itype_id (subtract_hd itype_id_eqb req_ids asn_ids)) <|
      ftype'_join <uj$>
      traverse_uj (intersect (unify_itype unify) asn_ids req_ids) <uj*>
      unify_stype' unify asn_struct req_struct
end.

Function unify' (asn: ftype) (req: ftype) {measure asn (ftype_depth asn)}: uj ftype :=
  unify_atype (unify_ntype (unify_ftype' unify')).

(* Old proof I abandoned which doesn't just use a measure function to show termination *)
(*
Definition uj'_has_fuel {A: Set} (a: uj' A): Prop :=
match a with
| UJ'OutOfFuel => False
| UJ' _ _ => True
end.

Definition uj'_has_fuel2 {A B: Set} (f: A -> A -> uj' B) (a0: A) (a1: A): Prop :=
  uj'_has_fuel (f a0 a1) /\ uj'_has_fuel (f a1 a0).

Definition uj'_has_fuel2' {A B C: Set} (g: B -> uj' C) (f: A -> A -> B) (a0: A) (a1: A): Prop :=
  uj'_has_fuel (g (f a0 a1)) /\ uj'_has_fuel (g (f a1 a0)).

Definition uj'_doesnt_affect_fuel {A B: Set} (f: uj' A -> uj' B): Prop := forall (a: uj' A), uj'_has_fuel a = uj'_has_fuel (f a).

Ltac uj'_doesnt_affect_fuel_start f :=
  unfold uj'_doesnt_affect_fuel, f;
  intros.

Ltac uj'_doesnt_affect_fuel_finish :=
  match goal with
  | a: uj' |- _ => destruct a; simpl; reflexivity
  end.

Lemma uj'_has_fuel_cons: forall {A: Set} err, uj'_doesnt_affect_fuel A A (uj'_cons err).
Proof.
  uj'_doesnt_affect_fuel_start uj'_cons.
  uj'_doesnt_affect_fuel_finish.
Qed.

Lemma uj'_has_fuel_loc_errs: forall {A: Set} errs, uj'_doesnt_affect_fuel A A (@loc_uj'_errs A errs).
Proof.
  uj'_doesnt_affect_fuel_start @loc_uj'_errs.
  uj'_doesnt_affect_fuel_finish.
Qed.

Lemma uj'_has_fuel_cons_iff: forall {A: Set} err cond, uj'_doesnt_affect_fuel A A (uj'_cons_iff err cond).
Proof.
  uj'_doesnt_affect_fuel_start uj'_cons_iff.
  destruct cond; uj'_doesnt_affect_fuel_finish.
Qed.

Lemma uj'_has_fuel_cons_map: forall {type A: Set} err cond, uj'_doesnt_affect_fuel type type (uj'_cons_map type A err cond).
Proof.
  uj'_doesnt_affect_fuel_start uj'_cons_map.
  destruct cond; uj'_doesnt_affect_fuel_finish.
Qed.

Lemma uj'_has_fuel_map: forall {A B: Set} f, uj'_doesnt_affect_fuel A B (@map_uj' A B f).
Proof.
  uj'_doesnt_affect_fuel_start @map_uj'.
  uj'_doesnt_affect_fuel_finish.
Qed.

Lemma uj'_has_fuel_ap: forall {A B: Set} f a, uj'_has_fuel f /\ uj'_has_fuel a <-> uj'_has_fuel (@ap_uj' A B f a).
Proof.
  uj'_doesnt_affect_fuel_start @ap_uj'.
  destruct f; destruct a; simpl; by_ intuition.
Qed.

Lemma uj'_has_fuel_transpose_option: forall {A: Set} a, Option_Forall uj'_has_fuel a <-> uj'_has_fuel (@transpose_option_uj' A a).
Proof.
  uj'_doesnt_affect_fuel_start @transpose_option_uj'.
  destruct a; simpl.
  - rewrite <- uj'_has_fuel_map. split.
    + intros H. inv H.  exact H2.
    + intros H. apply Option_Forall_Some. exact H.
  - split.
    + reflexivity.
    + intros _. apply Option_Forall_None.
Qed.

Lemma uj'_has_fuel_traverse: forall {A: Set} xs, List.Forall uj'_has_fuel xs <-> uj'_has_fuel (@traverse_uj' A xs).
Proof.
  uj'_doesnt_affect_fuel_start @traverse_uj'.
  induction xs; simpl.
    by_ intuition.
  fold (@traverse_uj' A). fold (@traverse_uj' A) in IHxs.
  intuition.
  - rewrite <- uj'_has_fuel_ap, <- uj'_has_fuel_map.
    inv H1.
    by_ intuition.
  - rewrite <- uj'_has_fuel_ap, <- uj'_has_fuel_map in H1.
    by_ intuition.
Qed.

Lemma uj'_has_fuel_traverse_loc_fields: forall {A: Set} loc xs,
 List.Forall (fun a => uj'_has_fuel (snd a)) xs <-> uj'_has_fuel (@traverse_loc_uj'_fields A loc xs).
Proof.
  uj'_doesnt_affect_fuel_start @traverse_loc_uj'_fields.
  induction xs; simpl.
    by_ intuition.
  fold (@traverse_loc_uj'_fields A loc). fold (@traverse_loc_uj'_fields A loc) in IHxs.
  intuition.
  - rewrite <- uj'_has_fuel_ap, <- uj'_has_fuel_map, <- uj'_has_fuel_loc_errs, <- uj'_has_fuel_map.
    inv H1.
    by_ intuition.
  - rewrite <- uj'_has_fuel_ap, <- uj'_has_fuel_map, <- uj'_has_fuel_loc_errs, <- uj'_has_fuel_map in H1.
    by_ intuition.
Qed.

Lemma uj'_has_fuel___traverse_loc_succ: forall {A: Set} xs loc0 idx0 loc1 idx1,
 uj'_has_fuel (@_traverse_loc_uj' A loc0 idx0 xs) <-> uj'_has_fuel (@_traverse_loc_uj' A loc1 idx1 xs).
Proof.
  intros A xs.
  induction xs; simpl; [by_ intuition |].
  intros.
  repeat rewrite <- uj'_has_fuel_ap, <- uj'_has_fuel_map, <- uj'_has_fuel_loc_errs.
  intuition; apply (IHxs loc0 (S idx0) loc1 (S idx1)); exact H1.
Qed.

Lemma uj'_has_fuel___traverse_loc: forall {A: Set} loc idx xs, List.Forall uj'_has_fuel xs <-> uj'_has_fuel (@_traverse_loc_uj' A loc idx xs).
Proof.
  uj'_doesnt_affect_fuel_start @_traverse_loc_uj'.
  induction xs; simpl.
    by_ intuition.
  fold (@_traverse_loc_uj' A). fold (@_traverse_loc_uj' A) in IHxs.
  intuition.
  - rewrite <- uj'_has_fuel_ap, <- uj'_has_fuel_map, <- uj'_has_fuel_loc_errs.
    inv H1.
    split; [exact H4 |].
    apply (uj'_has_fuel___traverse_loc_succ xs loc idx loc (S idx)). exact (H H5).
  - apply List.Forall_cons.
    + rewrite <- uj'_has_fuel_ap, <- uj'_has_fuel_map, <- uj'_has_fuel_loc_errs in H1.
      destruct H1. exact H1.
    + apply H0.
      rewrite <- uj'_has_fuel_ap, <- uj'_has_fuel_map, <- uj'_has_fuel_loc_errs in H1.
      destruct H1. apply (uj'_has_fuel___traverse_loc_succ xs loc (S idx) loc idx). exact H2.
Qed.

Lemma uj'_has_fuel_traverse_loc: forall {A: Set} loc xs, List.Forall uj'_has_fuel xs <-> uj'_has_fuel (@traverse_loc_uj' A loc xs).
Proof.
  unfold traverse_loc_uj'.
  intros.
  exact (uj'_has_fuel___traverse_loc A loc 0 xs).
Qed.

Lemma uj'_has_fuel_ftype_join: forall ids s,
  (List.Forall uj'_has_fuel ids /\ (Option_Forall (fun x => uj'_has_fuel (fst x)) s \/ ids <> nil) <-> uj'_has_fuel (uj'_ftype_join ids s)).
Proof.
  uj'_doesnt_affect_fuel_start uj'_ftype_join.
  split.
  - intros [H0 H1].
    destruct ids.
    + destruct s as [[s req_s] |].
      * inv H1; [| contradiction]. inv H. simpl in H3.
        rewrite <- uj'_has_fuel_map. exact H3.
      * by_ simpl.
    + rewrite <- uj'_has_fuel_map, <- uj'_has_fuel_ap, <- uj'_has_fuel_map, <- uj'_has_fuel_traverse.
      inv H0. split; [exact H3 | exact H4].
  - destruct ids.
    + split.
        apply List.Forall_nil.
      left.
      destruct s as [[s req_s] |].
      * rewrite <- uj'_has_fuel_map in H.
        apply Option_Forall_Some. simpl.
        exact H.
      * apply Option_Forall_None.
    + rewrite <- uj'_has_fuel_map, <- uj'_has_fuel_ap, <- uj'_has_fuel_map, <- uj'_has_fuel_traverse.
      intros [H0 H1].
      split.
        apply List.Forall_cons; [exact H0 | exact H1].
      right.
      discriminate.
Qed.

Lemma uj'_has_fuel_then: forall {A B: Set} f a,
 ((forall b, uj'_has_fuel (f b)) /\ uj'_has_fuel a -> uj'_has_fuel (@then_uj' A B f a)) /\
 (uj'_has_fuel (@then_uj' A B f a) -> (exists b, uj'_has_fuel (f b)) /\ uj'_has_fuel a).
Proof.
  uj'_doesnt_affect_fuel_start @then_uj'.
  destruct a; simpl; try by_ intuition.
  split.
  - intros [H _].
    specialize (H union).
    destruct (f union); [contradiction H | by_ simpl].
  - intros H.
    split; try reflexivity.
    exists union.
    destruct (f union); [contradiction H | by_ simpl].
Qed.

Ltac simpl_uj'_has_fuel :=
  repeat (rewrite
      <- ? uj'_has_fuel_cons,
      <- ? uj'_has_fuel_loc_errs,
      <- ? uj'_has_fuel_cons_iff,
      <- ? uj'_has_fuel_cons_map,
      <- ? uj'_has_fuel_map,
      <- ? uj'_has_fuel_ap,
      <- ? uj'_has_fuel_traverse,
      <- ? uj'_has_fuel_traverse_loc,
      <- ? uj'_has_fuel_traverse_loc_fields,
      <- ? uj'_has_fuel_transpose_option,
      <- ? uj'_has_fuel_ftype_join,
      <- ? uj'_has_fuel_then).

Lemma fold_unify'_fuel: forall (fuel: nat),
 (unify' (S fuel)) = (unify_atype (unify_ntype (unify_ftype' (unify' fuel)))).
Proof.
  intros fuel.
  apply functional_extensionality. intros a. apply functional_extensionality. intros b.
  simpl. reflexivity.
Qed.

Ltac fold_unify' := rewrite <- fold_unify'_fuel.
Ltac fold_unify'_in H := rewrite <- fold_unify'_fuel in H.

Lemma unify'_fuel_succ: forall (fuel: nat) (a b: ftype), uj'_has_fuel (unify' fuel a b) -> uj'_has_fuel (unify' (S fuel) a b).
Proof.
  intros fuel. induction fuel; simpl.
    contradiction.
  simpl in IHfuel.
  intros a b.
  unfold unify_atype; destruct a; destruct b; simpl; try reflexivity.
  fold (@unify_atype ftype' (unify_ntype (unify_ftype' (unify' fuel)))).
  rename nullable into a_nullable, a0 into b, nullable0 into b_nullable.
  simpl_uj'_has_fuel.
  clear a_nullable. clear b_nullable.
  unfold unify_ntype; destruct a; destruct b; simpl; try reflexivity.
  fold (@unify_ntype ftype' (unify_ftype' (unify' fuel))).
  rename a0 into b.
  simpl_uj'_has_fuel.
  unfold unify_ftype'; destruct a; destruct b.
  fold (unify_ftype' (unify' fuel)).
  rename ids into a_ids, s into a_struct, ids0 into b_ids, s0 into b_struct.
  simpl_uj'_has_fuel.
  intros [H0 H1]. split.
  - apply (forall_intersect (unify_itype (unify' fuel))).
    + intros [a_ident a_targs] [b_ident b_targs]. unfold unify_itype.
      destruct (negb (a_ident =? b_ident)%string); [reflexivity | discriminate].
    + intros [a_ident a_args] [b_ident b_targs] H2. unfold unify_itype.
      destruct (negb (a_ident =? b_ident)%string); intros H3; [exact H3 |].
      inv H3. apply Option_Forall_Some.
      revert H5.
      simpl_uj'_has_fuel.
      apply forall_zip_with.
      exact IHfuel.
    + exact H0.
  - destruct H1; [left | right].
    + revert H. apply forall_option_zip_with.
      simpl.
      intros a b.
      unfold unify_stype; destruct a; destruct b; simpl; try reflexivity;
      simpl_uj'_has_fuel.
      * split; [split |]; [destruct H as [[H _] _] | destruct H as [[_ H] _] | destruct H as [_ H]]; revert H.
          apply forall_zip_with. exact IHfuel.
          apply forall_option_zip_with. exact IHfuel.
        unfold unify_vtype; destruct ret; destruct ret0; simpl; try reflexivity.
        simpl_uj'_has_fuel.
        exact (IHfuel a a0).
      * exact (IHfuel elem elem0).
      * apply forall_zip_with. exact IHfuel.
      * simpl_uj'_has_fuel.
        apply forall_js_record_zip_with. exact IHfuel.
    + revert H. apply non_empty_intersect.
      intros a b.
      unfold unify_itype. destruct a; destruct b.
      destruct (negb (name =? name0)%string); [reflexivity | discriminate].
Qed.

Ltac prove_unify'_fuel2_succ succ :=
  intros fuel a b; unfold uj'_has_fuel2;
  intros H; split; [destruct H as [H _] | destruct H as [_ H]];
    apply succ; exact H.

Lemma unify'_fuel2_succ: forall (fuel: nat) (a b: ftype), uj'_has_fuel2 (unify' fuel) a b -> uj'_has_fuel2 (unify' (S fuel)) a b.
Proof.
  prove_unify'_fuel2_succ unify'_fuel_succ.
Qed.

Lemma unify'_fuel_vtype_succ: forall (fuel: nat) (a b: vtype ftype),
 uj'_has_fuel (unify_vtype (unify' fuel) a b) -> uj'_has_fuel (unify_vtype (unify' (S fuel)) a b).
Proof.
  intros fuel a b.
  destruct a; destruct b; simpl; try reflexivity; simpl_uj'_has_fuel.
  fold_unify'. exact (unify'_fuel_succ fuel a a0).
Qed.

Lemma unify'_fuel_itype_succ: forall (fuel: nat) (a b: itype ftype),
 Option_Forall uj'_has_fuel (unify_itype (unify' fuel) a b) -> Option_Forall uj'_has_fuel (unify_itype (unify' (S fuel)) a b).
Proof.
  intros fuel [a_name a_targs] [b_name b_targs].
  simpl.
  destruct (negb (a_name =? b_name)%string); intros H; [apply Option_Forall_None | apply Option_Forall_Some]; inv H; revert H2.
  simpl_uj'_has_fuel. fold_unify'.
  apply forall_zip_with. exact (unify'_fuel_succ fuel).
Qed.

Lemma unify'_fuel_stype_succ: forall (fuel: nat) (a b: stype ftype),
 uj'_has_fuel (unify_stype (unify' fuel) a b) -> uj'_has_fuel (unify_stype (unify' (S fuel)) a b).
Proof.
  intros fuel a b.
  destruct a; destruct b; simpl; try reflexivity; simpl_uj'_has_fuel.
  - intros H.
    split; [split |].
    + destruct H as [[H _] _].
      revert H. fold_unify'.
      apply forall_zip_with. exact (unify'_fuel_succ fuel).
    + destruct H as [[_ H] _].
      revert H. fold_unify'.
      apply forall_option_zip_with. exact (unify'_fuel_succ fuel).
    + destruct H as [_ H].
      revert H. fold_unify'.
      exact (unify'_fuel_vtype_succ fuel ret ret0).
  - fold_unify'. exact (unify'_fuel_succ fuel elem elem0).
  - fold_unify'.
    apply forall_zip_with. exact (unify'_fuel_succ fuel).
  - fold_unify'.
    apply forall_js_record_zip_with. exact (unify'_fuel_succ fuel).
Qed.

Lemma unify'_fuel_ftype'_succ: forall (fuel: nat) (a b: ftype'),
 uj'_has_fuel (unify_ftype' (unify' fuel) a b) -> uj'_has_fuel (unify_ftype' (unify' (S fuel)) a b).
Proof.
  intros fuel [a_ids a_struct] [b_ids b_struct].
  simpl. simpl_uj'_has_fuel.
  intros H.
  split.
  - destruct H as [H _].
    revert H. apply forall_intersect.
    + intros [a_name a_targs] [b_name b_targs].
      simpl.
      destruct (negb (a_name =? b_name)%string); [reflexivity | discriminate].
    + intros a b _.
      fold_unify'. exact (unify'_fuel_itype_succ fuel a b).
  - destruct H as [_ H].
    destruct H as [H | H]; [left | right].
    + revert H. apply forall_option_zip_with.
      simpl. fold_unify'. exact (unify'_fuel_stype_succ fuel).
    + revert H. apply non_empty_intersect.
      intros [a_ids0 a_struct0] [b_ids0 b_struct0].
      simpl.
      destruct (negb (a_ids0 =? b_ids0)%string); [reflexivity | discriminate].
Qed.

Ltac prove_unify'_fuel_more succ :=
  intros fuel more_fuel a b rel;
  elim rel; [intros H; exact H |];
  intros more_fuel0 rel0 IHrel H; specialize (IHrel H);
  apply succ; exact IHrel.

Lemma unify'_fuel_more: forall (fuel more_fuel: nat) (a b: ftype), fuel <= more_fuel ->
 uj'_has_fuel (unify' fuel a b) -> uj'_has_fuel (unify' more_fuel a b).
Proof.
  prove_unify'_fuel_more unify'_fuel_succ.
Qed.

Lemma unify'_fuel_vtype_more: forall (fuel more_fuel: nat) (a b: vtype ftype), fuel <= more_fuel ->
 uj'_has_fuel (unify_vtype (unify' fuel) a b) -> uj'_has_fuel (unify_vtype (unify' more_fuel) a b).
Proof.
  prove_unify'_fuel_more unify'_fuel_vtype_succ.
Qed.

Lemma unify'_fuel_itype_more: forall (fuel more_fuel: nat) (a b: itype ftype), fuel <= more_fuel ->
 Option_Forall uj'_has_fuel (unify_itype (unify' fuel) a b) -> Option_Forall uj'_has_fuel (unify_itype (unify' more_fuel) a b).
Proof.
  prove_unify'_fuel_more unify'_fuel_itype_succ.
Qed.

Lemma unify'_fuel_stype_more: forall (fuel more_fuel: nat) (a b: stype ftype), fuel <= more_fuel ->
 uj'_has_fuel (unify_stype (unify' fuel) a b) -> uj'_has_fuel (unify_stype (unify' more_fuel) a b).
Proof.
  prove_unify'_fuel_more unify'_fuel_stype_succ.
Qed.

Ltac specialize_unify'_succ f H := specialize (f _ _ _ H); clear H; intros H.

Lemma unify'_has_fuel': forall (a b: ftype), exists (fuel: nat), uj'_has_fuel (unify' fuel a b) /\ uj'_has_fuel (unify' fuel b a).
Proof.
  apply (ftype_ind'
    (fun a => forall b, exists fuel, uj'_has_fuel2 (unify' fuel) a b)
    (fun a => forall b, exists fuel, uj'_has_fuel2 (unify_ntype (unify_ftype' (unify' fuel))) a b)
    (fun a => forall b, exists fuel, uj'_has_fuel2 (unify_ftype' (unify' fuel)) a b)
    (fun a => forall b, exists fuel, uj'_has_fuel2' transpose_option_uj' (unify_itype (unify' fuel)) a b)
    (fun a => forall b, exists fuel, uj'_has_fuel2 (unify_stype (unify' fuel)) a b)
    (fun a => forall b, exists fuel, uj'_has_fuel2 (unify_vtype (unify' fuel)) a b)
    (fun a => forall b, exists fuel, uj'_has_fuel2' transpose_option_uj' (option_zip_with (unify_stype (unify' fuel))) a b)
    (fun a => forall b, exists fuel, uj'_has_fuel2' transpose_option_uj' (option_zip_with (unify' fuel)) a b)
    (fun a => forall b, exists fuel, uj'_has_fuel2' traverse_uj' (intersect (unify_itype (unify' fuel))) a b)
    (fun a => forall b, exists fuel, uj'_has_fuel2' traverse_uj' (zip_with (unify' fuel)) a b));
    intros.
  - exists 1. simpl. destruct b as [| b_n b]; split; by_ simpl.
  - destruct b as [| b_n b].
    + exists 1. split; by_ simpl.
    + specialize (H b). destruct H as [fuel H]. exists (S fuel).
      destruct H as [H0 H1].
      remember (unify_ntype (unify_ftype' (unify' fuel)) a b) as x. destruct x. contradiction H0.
      remember (unify_ntype (unify_ftype' (unify' fuel)) b a) as y. destruct y. contradiction H1.
      unfold uj'_has_fuel2. simpl. rewrite <- Heqx, <- Heqy. simpl_uj'_has_fuel. split; by_ simpl.
  - exists 1. split; destruct b; by_ simpl.
  - destruct b as [| b].
    + exists 1. split; by_ simpl.
    + specialize (H b). destruct H as [fuel [H0 H1]]. exists (S fuel).
      split; simpl; simpl_uj'_has_fuel; fold_unify'; [revert H0 | revert H1]; apply unify'_fuel_ftype'_succ.
  - rename H into IHids, H0 into IHs, ids into a_ids, s into a_struct. destruct b as [b_ids b_struct].
    specialize (IHids b_ids). specialize (IHs b_struct). destruct IHids as [id_fuel [IHids0 IHids1]]. destruct IHs as [s_fuel [IHs0 IHs1]].
    remember (max id_fuel s_fuel) as fuel. exists fuel.
    split; [rename IHids0 into IHids, IHs0 into IHs; clear IHids1; clear IHs1 | rename IHids1 into IHids, IHs1 into IHs; clear IHids0; clear IHs0].
    all: revert IHids; revert IHs; simpl_uj'_has_fuel; intros IHs IHids.
    all: apply (forall_option_zip_with _ (unify_stype (unify' fuel))) in IHs.
    2, 4: intros a b.
    2, 3: apply unify'_fuel_stype_more.
    2, 3: rewrite Heqfuel.
    2, 3: apply Nat.le_max_r.
    all: apply (forall_intersect _ (unify_itype (unify' fuel))) in IHids.
    2, 5: intros [a_id a_targs] [b_id b_targs].
    2, 3: simpl.
    2, 3: destruct (negb (a_id =? b_id)%string); [reflexivity | discriminate].
    2, 4: intros a b _.
    2, 3: apply unify'_fuel_itype_more.
    2, 3: rewrite Heqfuel.
    2, 3: apply Nat.le_max_l.
    all: simpl; simpl_uj'_has_fuel.
    all: split; [exact IHids |].
    all: left.
    all: revert IHs.
    all: apply forall_option_zip_with'.
    all: intros a b H; simpl; exact H.
  - rename H into IHtargs, name into a_name, targs into a_targs. destruct b as [b_name b_targs].
    specialize (IHtargs b_targs). destruct IHtargs as [fuel [IHtargs0 IHtargs1]]. exists fuel.
    split; [rename IHtargs0 into IHtargs; clear IHtargs1 | rename IHtargs1 into IHtargs; clear IHtargs0].
    all: simpl; revert IHtargs; simpl_uj'_has_fuel; intros IHtargs.
    1: destruct (negb (a_name =? b_name)%string); [apply Option_Forall_None | apply Option_Forall_Some].
    2: destruct (negb (b_name =? a_name)%string); [apply Option_Forall_None | apply Option_Forall_Some].
    all: simpl_uj'_has_fuel; exact IHtargs.
  - destruct b; try (exists 0; split; by_ simpl).
    rename H into IHparams, H0 into IHrparam, H1 into IHret.
    rename tparams into a_tparams, params into a_params, rparam into a_rparam, ret into a_ret.
    rename tparams0 into b_tparams, params0 into b_params, rparam0 into b_rparam, ret0 into b_ret.
    specialize (IHparams b_params). specialize (IHrparam b_rparam). specialize (IHret b_ret).
    destruct IHparams as [params_fuel [IHparams0 IHparams1]].
    destruct IHrparam as [rparam_fuel [IHrparam0 IHrparam1]].
    destruct IHret as [ret_fuel [IHret0 IHret1]].
    remember (max params_fuel (max rparam_fuel ret_fuel)) as fuel. exists fuel.
    split.
    1: rename IHparams1 into IHparams, IHrparam1 into IHrparam, IHret0 into IHret; clear IHparams0; clear IHrparam0; clear IHret1.
    2: rename IHparams0 into IHparams, IHrparam0 into IHrparam, IHret1 into IHret; clear IHparams1; clear IHrparam1; clear IHret0.
    all: simpl; revert IHparams; revert IHrparam; revert IHret; simpl_uj'_has_fuel; intros IHret IHrparam IHparams.
    all: apply (forall_zip_with _ (unify' fuel)) in IHparams; [|
      intros a b;
      apply unify'_fuel_more;
      rewrite Heqfuel;
      apply Nat.le_max_l].
    all: apply (forall_option_zip_with _ (unify' fuel)) in IHrparam; [|
      intros a b;
      apply unify'_fuel_more;
      rewrite Heqfuel;
      rewrite Nat.max_assoc, Nat.max_comm, Nat.max_assoc, Nat.max_comm;
      apply Nat.le_max_l].
    all: apply (@unify'_fuel_vtype_more _ fuel _ _) in IHret; [|
      rewrite Heqfuel;
      rewrite Nat.max_assoc;
      apply Nat.le_max_r].
    all: split; [split |].
    1, 4: exact IHparams.
    1, 3: exact IHrparam.
    1, 2: exact IHret.
  - destruct b; try (exists 0; split; by_ simpl).
    rename H into IHelem, elem into a_elem, elem0 into b_elem.
    specialize (IHelem b_elem). destruct IHelem as [fuel [IHelem0 IHelem1]]. exists fuel.
    split; simpl; simpl_uj'_has_fuel; [exact IHelem0 | exact IHelem1].
  -
*)
