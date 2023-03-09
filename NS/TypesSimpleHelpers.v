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

Definition map_itype {A B: Set} (f: A -> B) (a: itype A): itype B :=
match a with
| I name targs => I name (List.map f targs)
end.

Definition map_vtype {A B: Set} (f: A -> B) (a: vtype A): vtype B :=
match a with
| VVoid => VVoid
| V a => V (f a)
end.

Definition map_tparam {A B: Set} (f: A -> B) (a: tparam A): tparam B :=
match a with
| TParam v name supers => TParam v name (List.map f supers)
end.

Definition map_otype {A B: Set} (f: A -> B) (a: otype A): otype B :=
match a with
| O nullable a => O nullable (f a)
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

Definition is_ftype_nullable (a: ftype): bool :=
match a with
| FAny => true
| FNever nullable => nullable
| FStructural nullable _ => nullable
| FNominal nullable _ _ _ => nullable
end.

Definition ttype_add_null_if (cond: bool) (a: ttype): ttype :=
match a with
| TAny => TAny
| TNever nullable => TNever (cond || nullable)
| TStructural nullable s => TStructural (cond || nullable) s
| TNominal nullable id => TNominal (cond || nullable) id
end.

Definition ftype_add_null_if (cond: bool) (a: ftype): ftype :=
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

Definition ftype_collapse_opt (nullable: bool) (a: option ftype): ftype :=
match a with
| None => FAny
| Some a => a
end.

Definition itype_id {type: Set} (a: itype type): string :=
match a with
| I name _ => name
end.

Definition itype_targs {type: Set} (a: itype type): list type :=
match a with
| I _ targs => targs
end.

Definition vtype_depth {type: Set} (type_depth: type -> nat) (a: vtype type): nat :=
match a with
| VVoid => 0
| V a => type_depth a
end.

Definition otype_depth {type: Set} (type_depth: type -> nat) (a: otype type): nat :=
match a with
| O _ a => type_depth a
end.

Definition tparam_depth {type: Set} (type_depth: type -> nat) (a: tparam type): nat :=
match a with
| TParam _ _ supers => list_max (List.map type_depth supers)
end.

Definition itype_depth {type: Set} (type_depth: type -> nat) (a: itype type): nat :=
match a with
| I _ targs => list_max (List.map type_depth targs)
end.

Definition stype_depth {type: Set} (type_depth: type -> nat) (a: stype type): nat :=
match a with
| SFn tparams thisp params rparam ret => list_max (
    type_depth thisp ::
    type_depth rparam ::
    vtype_depth type_depth ret ::
    List.map (tparam_depth type_depth) tparams ++
    List.map (otype_depth type_depth) params)%list
| SArray elem => type_depth elem
| STuple elems => list_max (List.map (otype_depth type_depth) elems)
| SObject fields => list_max (List.map (otype_depth type_depth << snd) fields)
end.

Fixpoint ttype_depth (a: ttype): nat := S (
match a with
| TAny => 0
| TNever _ => 0
| TStructural _ s => stype_depth ttype_depth s
| TNominal _ id => itype_depth ttype_depth id
end).

Fixpoint ftype_depth (a: ftype): nat := S (
match a with
| FAny => 0
| FNever _ => 0
| FStructural _ s => stype_depth ftype_depth s
| FNominal _ id sids s => list_max (itype_depth ftype_depth id :: option_map (stype_depth ftype_depth) s ?:: List.map (itype_depth ftype_depth) sids)
end).
