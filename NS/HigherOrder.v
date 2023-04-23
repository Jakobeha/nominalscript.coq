(* Add LoadPath should not be necessary but it is *)
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Definitions.
From NS Require Import Misc.

Class Forall (F: Set -> Set) := forall_: forall {A: Set} (P: A -> Prop), F A -> Prop.

Global Instance Forall_option: Forall option := @Option_Forall.
Global Instance Forall_list: Forall list := @List.Forall.
