(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
From NS Require Import Misc.
From NS Require Import TypesBase.
From NS Require Import TypesNotation.

Definition ftype'_struct (a: ftype'): option (stype ftype) :=
match a with
| FTypeStructural s => Some s
| FTypeNominal _ _ s => s
end.

Definition ftype'_nominal (a: ftype'): list (itype ftype) :=
match a with
| FTypeStructural _ => nil
| FTypeNominal hd tl _ => cons hd tl
end.

Definition ftype'_split (a: ftype'): list (itype ftype) * option (stype ftype) :=
match a with
| FTypeStructural s => (nil, Some s)
| FTypeNominal id super_ids s => (cons id super_ids, s)
end.

Definition ftype'_join (ids: list (itype ftype)) (s: option (stype ftype)): option ftype' :=
match ids, s with
| nil, None => None
| nil, Some s => Some (FTypeStructural s)
| cons id ids, s => Some (FTypeNominal id ids s)
end.

Definition map_itype {A B: Set} (f: A -> B) (a: itype A): itype B :=
match a with
| IType name targs => IType name (List.map f targs)
end.

Definition map_vtype {A B: Set} (f: A -> B) (a: vtype A): vtype B :=
match a with
| VVoid => VVoid
| VType a => VType (f a)
end.

Definition map_stype {A B: Set} (f: A -> B) (a: stype A): stype B :=
match a with
| SFn tparams params rparam ret => SFn tparams (List.map f params) (option_map f rparam) (map_vtype f ret)
| SArray elem => SArray (f elem)
| STuple elems => STuple (List.map f elems)
| SObject fields => SObject (map_js_record f fields)
end.

Definition map_ntype {A B: Set} (f: A -> B) (a: ntype A): ntype B :=
match a with
| NNever => NNever
| NType a => NType (f a)
end.

Definition map_atype {A B: Set} (f: A -> B) (a: atype A): atype B :=
match a with
| AAny => AAny
| AType nullable a => AType nullable (map_ntype f a)
end.

Definition map_opt_atype {A B: Set} (f: A -> option B) (a: atype A): atype B :=
match a with
| AAny => AAny
| AType nullable a =>
   match map_ntype f a with
   | NNever => AType nullable NNever
   | NType None => AAny
   | NType (Some b) => AType nullable (NType b)
   end
end.

Fixpoint thin' (a: ftype'): ttype' :=
match a with
| FTypeStructural s => TTypeStructural (map_stype (map_atype thin') s)
| FTypeNominal id _ _ => TTypeNominal (map_itype (map_atype thin') id)
end.
Notation thin := (map_atype thin').

Definition is_nullable {type: Set} (a: atype type): bool :=
match a with
| AAny => true
| AType nullable _ => nullable
end.

Definition add_null_if {type: Set} (cond: bool) (a: atype type): atype type :=
match a with
| AAny => AAny
| AType nullable a => AType (nullable || cond) a
end.

Definition atype_opt {type: Set} (nullable: bool) (a: option (ntype type)): atype type :=
match a with
| None => AAny
| Some a => AType nullable a
end.

Definition itype_id {type: Set} (a: itype type): string :=
match a with
| IType name _ => name
end.

Definition itype_targs {type: Set} (a: itype type): list type :=
match a with
| IType _ targs => targs
end.

Definition ntype_depth {type: Set} (type_depth: type -> nat) (a: ntype type): nat :=
match a with
| NNever => 0
| NType a => type_depth a
end.

Definition atype_depth {type: Set} (type_depth: type -> nat) (a: atype type): nat :=
match a with
| AAny => 0
| AType _ a => ntype_depth type_depth a
end.

Definition vtype_depth {type: Set} (type_depth: type -> nat) (a: vtype type): nat :=
match a with
| VVoid => 0
| VType a => type_depth a
end.

Definition itype_depth {type: Set} (type_depth: type -> nat) (a: itype type): nat :=
match a with
| IType _ targs => list_max (List.map type_depth targs)
end.

Definition stype_depth {type: Set} (type_depth: type -> nat) (a: stype type): nat :=
match a with
| SFn _ params rparam ret => list_max (vtype_depth type_depth ret :: option_map type_depth rparam ?:: List.map type_depth params)%list
| SArray elem => type_depth elem
| STuple elems => list_max (List.map type_depth elems)
| SObject fields => list_max (List.map (type_depth << snd) fields)
end.

(* We can't define ftype'_depth before provind some lemmas that show it terminates. limit = fuel *)
Fixpoint ftype'_depth_upto (limit: nat) (a: ftype'): nat :=
match limit with
| O => 0
| S limit => S <|
  match ftype'_split a with
  | (ids, s) =>
     list_max (option_map (stype_depth (atype_depth (ftype'_depth_upto limit))) s ?::
     List.map (itype_depth (atype_depth (ftype'_depth_upto limit))) ids)
  end
end.
Notation ftype_depth_upto limit := (atype_depth (ftype'_depth_upto limit)).
