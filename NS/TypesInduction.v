(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Add LoadPath "tlc/src" as TLC.
Set Implicit Arguments.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
From TLC Require Import LibTactics.
From NS Require Import Misc.
From NS Require Import MiscArith.
From NS Require Import TypesBase.
From NS Require Import TypesNotation.
From NS Require Import TypesSimpleHelpers.

(* Mutually-inductive fat type where we actually have a usable (albeit huge) induction scheme *)
Inductive _ftype: Set :=
| _AAny
| _AType (nullable: bool) (a: _ntype)
with _ntype: Set :=
| _NNever
| _NType (a: _ftype')
with _ftype': Set :=
| _FTypeStructural (s: _stype)
| _FTypeNominal (id: _itype) (super_ids: _list_itype) (s: _option_stype)
with _itype: Set :=
| _IType (name: string) (targs: _list_ftype)
with _stype: Set :=
| _SFn (tparams: list string) (params: _list_ftype) (rparam: _option_ftype) (ret: _vtype)
| _SArray (elem: _ftype)
| _STuple (elems: _list_ftype)
| _SObject (fields: _js_record_ftype)
with _vtype: Set :=
| _VVoid
| _VType (a: _ftype)
with _option_stype: Set :=
| None_SType
| Some_SType (a: _stype)
with _option_ftype: Set :=
| None_FType
| Some_FType (a: _ftype)
with _list_itype: Set :=
| Nil_IType
| Cons_IType (x: _itype) (xs: _list_itype)
with _list_ftype: Set :=
| Nil_FType
| Cons_FType (x: _ftype) (xs: _list_ftype)
with _js_record_ftype: Set :=
| Nil_JsRecord_FType
| Cons_JsRecord_FType (x: _string_ftype) (xs: _js_record_ftype)
with _string_ftype: Set :=
| String_FType (key: string) (value: _ftype).

Scheme _ftype_rec' := Induction for _ftype Sort Set
with _ntype_rec' := Induction for _ntype Sort Set
with _ftype'_rec' := Induction for _ftype' Sort Set
with _itype_rec' := Induction for _itype Sort Set
with _stype_rec' := Induction for _stype Sort Set
with _vtype_rec' := Induction for _vtype Sort Set
with _option_stype_rec' := Induction for _option_stype Sort Set
with _option_ftype_rec' := Induction for _option_ftype Sort Set
with _list_itype_rec' := Induction for _list_itype Sort Set
with _list_ftype_rec' := Induction for _list_ftype Sort Set
with _js_record_ftype_rec' := Induction for _js_record_ftype Sort Set
with _string_ftype_rec' := Induction for _string_ftype Sort Set.

Scheme _ftype_ind' := Induction for _ftype Sort Prop
with _ntype_ind' := Induction for _ntype Sort Prop
with _ftype'_ind' := Induction for _ftype' Sort Prop
with _itype_ind' := Induction for _itype Sort Prop
with _stype_ind' := Induction for _stype Sort Prop
with _vtype_ind' := Induction for _vtype Sort Prop
with _option_stype_ind' := Induction for _option_stype Sort Prop
with _option_ftype_ind' := Induction for _option_ftype Sort Prop
with _list_itype_ind' := Induction for _list_itype Sort Prop
with _list_ftype_ind' := Induction for _list_ftype Sort Prop
with _js_record_ftype_ind' := Induction for _js_record_ftype Sort Prop
with _string_ftype_ind' := Induction for _string_ftype Sort Prop.


(* And then we define an Axiom for equivalence, so that we can actually induct on this *)
Axiom ftype_iso : ftype = ftype'.

(* Same as _ftype_rec' and _ftype_ind' but with the original fat type. *)
Check _ftype_rec'.
Check _ftype_ind'.
Axiom ftype_rec'
  : forall (P : ftype -> Set) (P0 : nftype -> Set) (P1 : ftype' -> Set) (P2 : iftype -> Set) (P3 : sftype -> Set) (P4 : vftype -> Set)
      (P5 : option sftype -> Set) (P6 : option ftype -> Set) (P7 : list iftype -> Set) (P8 : list ftype -> Set) (P9: js_record ftype -> Set)
      (P10 : string * ftype -> Set),
    P AAny ->
    (forall (nullable : bool) (a : nftype), P0 a -> P (AType nullable a)) ->
    P0 NNever ->
    (forall a : ftype', P1 a -> P0 (NType a)) ->
    (forall s : sftype, P3 s -> P1 (FTypeStructural s)) ->
    (forall id : iftype, P2 id -> forall super_ids : list iftype, P7 super_ids -> forall s :  option sftype, P5 s -> P1 (FTypeNominal id super_ids s)) ->
    (forall (name : string) (targs : list ftype), P8 targs -> P2 (IType name targs)) ->
    (forall (tparams : list string) (params : list ftype),
    P8 params -> forall rparam : option ftype, P6 rparam -> forall ret : vftype, P4 ret -> P3 (SFn tparams params rparam ret)) ->
    (forall elem : ftype, P elem -> P3 (SArray elem)) ->
    (forall elems : list ftype, P8 elems -> P3 (STuple elems)) ->
    (forall fields : js_record ftype, P9 fields -> P3 (SObject fields)) ->
    P4 VVoid ->
    (forall a : ftype, P a -> P4 (VType a)) ->
    P5 None ->
    (forall a : sftype, P3 a -> P5 (Some a)) ->
    P6 None ->
    (forall a : ftype, P a -> P6 (Some a)) ->
    P7 nil ->
    (forall x : iftype, P2 x -> forall xs : list iftype, P7 xs -> P7 (cons x xs)) ->
    P8 nil ->
    (forall x : ftype, P x -> forall xs : list ftype, P8 xs -> P8 (cons x xs)) ->
    P9 nil ->
    (forall x : string * ftype, P10 x -> forall xs : js_record ftype, P9 xs -> P9 (cons x xs)) ->
    (forall (key: string) (value: ftype), P value -> P10 (key, value)) ->
    forall f : ftype, P f.
Axiom ftype_ind'
  : forall (P : ftype -> Prop) (P0 : nftype -> Prop) (P1 : ftype' -> Prop) (P2 : iftype -> Prop) (P3 : sftype -> Prop) (P4 : vftype -> Prop)
      (P5 : option sftype -> Prop) (P6 : option ftype -> Prop) (P7 : list iftype -> Prop) (P8 : list ftype -> Prop) (P9: js_record ftype -> Prop)
      (P10 : string * ftype -> Prop),
    P AAny ->
    (forall (nullable : bool) (a : nftype), P0 a -> P (AType nullable a)) ->
    P0 NNever ->
    (forall a : ftype', P1 a -> P0 (NType a)) ->
    (forall s : sftype, P3 s -> P1 (FTypeStructural s)) ->
    (forall id : iftype, P2 id -> forall super_ids : list iftype, P7 super_ids -> forall s :  option sftype, P5 s -> P1 (FTypeNominal id super_ids s)) ->
    (forall (name : string) (targs : list ftype), P8 targs -> P2 (IType name targs)) ->
    (forall (tparams : list string) (params : list ftype),
    P8 params -> forall rparam : option ftype, P6 rparam -> forall ret : vftype, P4 ret -> P3 (SFn tparams params rparam ret)) ->
    (forall elem : ftype, P elem -> P3 (SArray elem)) ->
    (forall elems : list ftype, P8 elems -> P3 (STuple elems)) ->
    (forall fields : js_record ftype, P9 fields -> P3 (SObject fields)) ->
    P4 VVoid ->
    (forall a : ftype, P a -> P4 (VType a)) ->
    P5 None ->
    (forall a : sftype, P3 a -> P5 (Some a)) ->
    P6 None ->
    (forall a : ftype, P a -> P6 (Some a)) ->
    P7 nil ->
    (forall x : iftype, P2 x -> forall xs : list iftype, P7 xs -> P7 (cons x xs)) ->
    P8 nil ->
    (forall x : ftype, P x -> forall xs : list ftype, P8 xs -> P8 (cons x xs)) ->
    P9 nil ->
    (forall x : string * ftype, P10 x -> forall xs : js_record ftype, P9 xs -> P9 (cons x xs)) ->
    (forall (key: string) (value: ftype), P value -> P10 (key, value)) ->
    forall f : ftype, P f.

(* Arguments ftype_ind' (P P0 P1 P2 P3 P4 P5 P6 P7 P8)%function_scope f f0%function_scope f1 (f2 f3 f4 f5 f6 f7 f8)%function_scope f9
  f10%function_scope f11 f12%function_scope f13 f14%function_scope f15 f16%function_scope f17 f18%function_scope _f. *)

Definition ftype_size (a: ftype): nat.
Proof.
  apply (ftype_rec'
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat)
    (fun _ => nat));
    intros;
    repeat match goal with
    | H : nat |- _ => apply (fun n => Nat.add n H); clear H
    end;
    try exact 1.
  exact a.
Defined.

Local Ltac t :=
  repeat match goal with
  | H : ftype |- _ => apply (fun n => Nat.add n (ftype_size H)); clear H
  end.
Local Ltac d a := destruct a; t.
Local Ltac i a := induction a; t.

Definition ftype'_size (a: ftype'): nat.
Proof.
  d a.
  d s.
  d ret.
  d rparam.
  i params.
  exact 1.
  exact
  destruct a.
  - destruct s.
    + destruct ret.
      * destruct rparam.

      *
    + induction params.



Definition ftype_wf (a: ftype) (b: ftype): Prop :=
  ftype_size a < ftype_size b.

Require Coq.Program.Wf.
Program Fixpoint ftype_depth (a: ftype) {wf ftype_wf a}: nat := atype_depth (fun a =>
  match ftype'_split a with
  | (ids, s) =>
     list_max (option_map (stype_depth (fun a => ftype_depth a)) s ?::
     List.map (itype_depth (fun a => ftype_depth a)) ids)
  end) a.
Next Obligation.


Lemma vtype_depth0: forall (a: vftype), vtype_depth (fun _ => 0) a = 0.
Proof.
  destruct 0; by_ simpl.
Qed.

Lemma ntype_depth0: forall (a: nftype), ntype_depth (fun _ => 0) a = 0.
Proof.
  destruct 0; by_ simpl.
Qed.

Lemma atype_depth0: forall (a: ftype), atype_depth (fun _ => 0) a = 0.
Proof.
  destruct 0; simpl; [reflexivity | apply ntype_depth0].
Qed.

Lemma stype_depth0: forall (a: sftype), stype_depth (fun _ => 0) a = 0.
Proof.
  destruct 0; simpl.
  - destruct rparam; destruct ret; induction params; simpl; reflexivity || exact IHparams.
  - reflexivity.
  - induction elems; simpl; [reflexivity | exact IHelems].
  - induction fields; simpl; [reflexivity | exact IHfields].
Qed.

Lemma itype_depth0: forall (a: iftype), itype_depth (fun _ => 0) a = 0.
Proof.
  destruct 0; simpl.
  induction targs; simpl; [reflexivity | exact IHtargs].
Qed.

Lemma vtype_depth0': @vtype_depth ftype (fun _ => 0) = fun _ => 0.
Proof.
  apply functional_extensionality. exact vtype_depth0.
Qed.

Lemma ntype_depth0': @ntype_depth ftype' (fun _ => 0) = fun _ => 0.
Proof.
  apply functional_extensionality. exact ntype_depth0.
Qed.

Lemma atype_depth0': @atype_depth ftype' (fun _ => 0) = fun _ => 0.
Proof.
  apply functional_extensionality. exact atype_depth0.
Qed.

Lemma stype_depth0': @stype_depth ftype (fun _ => 0) = fun _ => 0.
Proof.
  apply functional_extensionality. exact stype_depth0.
Qed.

Lemma itype_depth0': @itype_depth ftype (fun _ => 0) = fun _ => 0.
Proof.
  apply functional_extensionality. exact itype_depth0.
Qed.

Print TypesSimpleHelpers.

(* Prove that the bounded measure function always has a higher bound to define an unbounded measure function *)
Lemma ftype'_depth_le_bound: forall (bound: nat),
  (forall a, ftype_depth_upto bound a <= bound) /\
  (forall a, ftype'_depth_upto bound a <= bound) /\
  (forall a, ntype_depth (ftype'_depth_upto bound) a <= bound) /\
  (forall a, stype_depth (ftype_depth_upto bound) a <= bound) /\
  (forall a, itype_depth (ftype_depth_upto bound) a <= bound) /\
  (forall a, vtype_depth (ftype_depth_upto bound) a <= bound) /\
  (forall a, option_max (option_map (stype_depth (ftype_depth_upto bound)) a) <= bound) /\
  (forall a, list_max (List.map (itype_depth (ftype_depth_upto bound)) a) <= bound) /\
  (forall a, option_max (option_map (ftype_depth_upto bound) a) <= bound) /\
  (forall a, list_max (List.map (ftype_depth_upto bound) a) <= bound).
Proof.
  intros bound. induction bound;
    [repeat split; simpl; intros a; rewrite
       ? atype_depth0',
       ? ntype_depth0',
       ? stype_depth0',
       ? itype_depth0',
       ? vtype_depth0',
       ? option_max_map0,
       ? list_max_map0; apply Nat.le_refl |].
  destruct IHbound as [If [If' [In [Is [Ii [Iv [Iso [Iil [Io Il]]]]]]]]].
  assert (forall a, ftype'_depth_upto (S bound) a <= S bound).
    intros a; destruct a; simpl; rewrite <- Nat.succ_le_mono.
      rewrite Nat.max_0_r. apply Is.
      rewrite list_max_cons_opt_le, list_max_cons_le. splits; [apply Iso | apply Ii | apply Iil].
  assert (forall a, ntype_depth (ftype'_depth_upto (S bound)) a <= S bound).
    intros a; destruct a; simpl; [apply Nat.le_0_l | simpl in H; exact (H a)].
  assert (forall a, ftype_depth_upto (S bound) a <= S bound).
    intros a; destruct a; simpl; [apply Nat.le_0_l | exact (H0 a)].
  assert (forall a, vtype_depth (ftype_depth_upto (S bound)) a <= S bound).
    intros a; destruct a; simpl; [apply Nat.le_0_l | simpl in H1; exact (H1 a)].
  assert (forall a, itype_depth (ftype_depth_upto (S bound)) a <= S bound).
    intros a; destruct a; simpl. apply list_max_map_all_le'. simpl in H1. exact H1.
  assert (forall a, stype_depth (ftype_depth_upto (S bound)) a <= S bound).
    intros a; destruct a; simpl.
      apply Nat.max_lub.
        simpl in H2. exact (H2 ret).
        rewrite list_max_cons_opt_le. split.
          apply option_max_map_all_le'. simpl in H1. exact H1.
          apply list_max_map_all_le'. simpl in H1. exact H1.
    simpl in H1. exact (H1 elem).
    apply list_max_map_all_le'. simpl in H1. exact H1.
    apply list_max_map_all_le'. intros [a_name a]. simpl. simpl in H1. exact (H1 a).
  repeat split.
  - exact H1.
  - exact H.
  - exact H0.
  - exact H4.
  - exact H3.
  - exact H2.
  - apply option_max_map_all_le'. exact H4.
  - apply list_max_map_all_le'. exact H3.
  - apply option_max_map_all_le'. exact H1.
  - apply list_max_map_all_le'. exact H1.
Qed.

Local Ltac specialize_bound H bound := specialize (H bound); assert_specialize H; [lia |].
Local Ltac exist_bound bound :=
  exists bound; intros bound' H; simpl.
Local Ltac destruct_bound' bound' :=
  destruct bound'; [lia |]; simpl.

Theorem ftype_depth_unbounded': forall (a: ftype), exists (bound: nat), forall (bound': nat), bound <= bound' -> ftype_depth_upto bound' a < bound.
Proof.
  apply (ftype_ind'
    (fun a => exists bound, forall bound', bound <= bound' -> ftype_depth_upto bound' a < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> ntype_depth (ftype'_depth_upto bound') a < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> ftype'_depth_upto bound' a < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> itype_depth (ftype_depth_upto bound') a < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> stype_depth (ftype_depth_upto bound') a < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> vtype_depth (ftype_depth_upto bound') a < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> option_max (option_map (stype_depth (ftype_depth_upto bound')) a) < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> option_max (option_map (ftype_depth_upto bound') a) < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> list_max (List.map (itype_depth (ftype_depth_upto bound')) a) < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> list_max (List.map (ftype_depth_upto bound') a) < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> list_max (List.map (ftype_depth_upto bound' << snd) a) < bound)
    (fun a => exists bound, forall bound', bound <= bound' -> ftype_depth_upto bound' (snd a) < bound));
    intros.
  (* This could *definitely* be automated. Honestly you could automate into one tactic and then use MetaCoq to
     automate generating the induction principle *)
  - exists 2. simpl. lia.
  - destruct H as [bound IH].
    exists bound. simpl. exact IH.
  - exists 2. simpl. lia.
  - destruct H as [bound IH].
    exists bound. simpl. exact IH.
  - destruct H as [bound IH].
    exist_bound (S bound). destruct_bound' bound'.
    specialize_bound IH bound'.
    lia.
  - destruct H as [id_bound IHid]. destruct H0 as [sids_bound IHsids]. destruct H1 as [s_bound IHs].
    pose (bound := Nat.max (Nat.max id_bound sids_bound) s_bound).
    exist_bound (S (S bound)). destruct_bound' bound'.
    specialize_bound IHid bound'. specialize_bound IHsids bound'. specialize_bound IHs bound'.
    rewrite <- Nat.succ_lt_mono, list_max_cons_opt_lt, list_max_cons_lt.
    lia.
  - destruct H as [bound IHtargs].
    exist_bound bound.
    specialize_bound IHtargs bound'.
    lia.
  - destruct H as [params_bound IHparams]. destruct H0 as [rparam_bound IHrparam]. destruct H1 as [ret_bound IHret].
    pose (bound := Nat.max (Nat.max params_bound rparam_bound) ret_bound).
    exist_bound (S bound).
    specialize_bound IHparams bound'. specialize_bound IHrparam bound'. specialize_bound IHret bound'.
    rewrite Nat.max_lub_lt_iff, list_max_cons_opt_lt.
    lia.
  - destruct H as [bound IHelem].
    exist_bound bound.
    specialize_bound IHelem bound'.
    lia.
  - destruct H as [bound IHelems].
    exist_bound bound.
    specialize_bound IHelems bound'.
    lia.
  - destruct H as [bound IHfields].
    exist_bound bound.
    specialize_bound IHfields bound'.
    lia.
  - exists 2. simpl. lia.
  - destruct H as [bound IH].
    exist_bound bound.
    specialize_bound IH bound'.
    lia.
  - exists 2. simpl. lia.
  - destruct H as [bound IH].
    exist_bound bound.
    specialize_bound IH bound'.
    lia.
  - exists 2. simpl. lia.
  - destruct H as [bound IH].
    exist_bound bound.
    specialize_bound IH bound'.
    lia.
  - exists 2. simpl. lia.
  - destruct H as [x_bound IHx]. destruct H0 as [xs_bound IHxs].
    pose (bound := Nat.max x_bound xs_bound).
    exist_bound bound.
    specialize_bound IHx bound'. specialize_bound IHxs bound'.
    lia.
  - exists 2. simpl. lia.
  - destruct H as [x_bound IHx]. destruct H0 as [xs_bound IHxs].
    pose (bound := Nat.max x_bound xs_bound).
    exist_bound bound.
    specialize_bound IHx bound'. specialize_bound IHxs bound'.
    lia.
  - exists 2. simpl. lia.
  - destruct H as [x_bound IHx]. destruct H0 as [xs_bound IHxs].
    pose (bound := Nat.max x_bound xs_bound).
    exist_bound bound.
    specialize_bound IHx bound'. specialize_bound IHxs bound'.
    lia.
  - destruct H as [bound IH].
    exist_bound bound.
    specialize_bound IH bound'.
    lia.
Qed.

Corollary ftype_depth_unbounded: forall (a: ftype), exists (bound: nat), ftype_depth_upto bound a < bound.
Proof.
  intros a.
  destruct (ftype_depth_unbounded' a) as [bound H].
  exists bound.
  exact (H bound (Nat.le_refl _)).
Qed.
