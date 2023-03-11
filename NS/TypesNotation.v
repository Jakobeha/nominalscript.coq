(* Add LoadPath should not be necessary but it is *)
Add LoadPath "." as NS.
Set Implicit Arguments.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
From NS Require Import TypesBase.

(* Parse and print types like in the language *)
Declare Scope ttype_scope.
Delimit Scope ttype_scope with ttype.
Bind Scope ttype_scope with ttype.
Declare Custom Entry ttype.
Declare Custom Entry ttype_field.
Declare Custom Entry ttype_ident.
Declare Custom Entry ttype_param.
Declare Custom Entry ottype.
Notation "[! x !]" := x (x custom ttype) : ttype_scope.
Notation "( x )" := x (in custom ttype, x custom ttype).
Notation "{! x !}" := x (in custom ttype, x constr).
Notation "'Any'" := TAny (in custom ttype).
Notation "'Never'" := (TNever false) (in custom ttype).
Notation "'Null'" := (TNever true) (in custom ttype).
Notation "x" := (TNominal false (It x nil)) (in custom ttype at level 0, x custom ttype_ident).
Notation "x ?" := (TNominal true (It x nil)) (in custom ttype at level 0, x custom ttype_ident).
Notation "x < x0 >" :=
  (TNominal false (It x (cons x0 nil)))
    (in custom ttype at level 0, x custom ttype_ident, x0 custom ttype at level 3).
Notation "x < x0 > ?" :=
  (TNominal true (It x (cons x0 nil)))
    (in custom ttype at level 0, x custom ttype_ident, x0 custom ttype at level 3).
Notation "x < x0 , .. , xn >" :=
  (TNominal false (It x (cons x0 .. (cons xn nil) .. )))
    (in custom ttype at level 0, x custom ttype_ident, x0 custom ttype at level 3, xn custom ttype at level 3).
Notation "x < x0 , .. , xn > ?" :=
  (TNominal true (It x (cons x0 .. (cons xn nil) .. )))
    (in custom ttype at level 0, x custom ttype_ident, x0 custom ttype at level 3, xn custom ttype at level 3).
Notation "x []" := (TStructural false (SArray x)) (in custom ttype at level 2, x custom ttype).
Notation "x [] ?" := (TStructural true (SArray x)) (in custom ttype at level 2, x custom ttype).
Notation "[ ]" := (TStructural false (STuple nil)) (in custom ttype).
Notation "[ ] ?" := (TStructural true (STuple nil)) (in custom ttype).
Notation "[ x0 ]" := (TStructural false (STuple (cons x0 nil))) (in custom ttype, x0 custom ottype at level 3).
Notation "[ x0 ] ?" := (TStructural true (STuple (cons x0 nil))) (in custom ttype, x0 custom ottype at level 3).
Notation "[ x0 , .. , xn ]" :=
  (TStructural false (STuple (cons x0 .. (cons xn nil) .. )))
    (in custom ttype, x0 custom ottype at level 3, xn custom ottype at level 3).
Notation "[ x0 , .. , xn ] ?" :=
  (TStructural true (STuple (cons x0 .. (cons xn nil) .. )))
    (in custom ttype, x0 custom ottype at level 3, xn custom ottype at level 3).
Notation "{ }" := (TStructural false (SObject nil)) (in custom ttype).
Notation "{ } ?" := (TStructural true (SObject nil)) (in custom ttype).
Notation "{ x0 }" := (TStructural false (SObject (cons x0 nil))) (in custom ttype, x0 custom ttype_field).
Notation "{ x0 } ?" := (TStructural true (SObject (cons x0 nil))) (in custom ttype, x0 custom ttype_field).
Notation "{ x0 , .. , xn }" :=
  (TStructural false (SObject (cons x0 .. (cons xn nil) .. )))
    (in custom ttype, x0 custom ttype_field, xn custom ttype_field).
Notation "{ x0 , .. , xn } ?" :=
  (TStructural true (SObject (cons x0 .. (cons xn nil) .. )))
    (in custom ttype, x0 custom ttype_field, xn custom ttype_field).
(* There are a *lot* of overloads for function types,
   because we need to define 3 variants for varargs (of which there are 2),
   2 variants for optional args, and 2 variants for "Void" or regular return value (though could define another custom entry here.)
   3 * 3 * 2 * 2 = 36, so we have 36 notations. At least none of them can be nullable without parenthesis___ *)
Notation "( ) => 'Void'" :=
  (TStructural false (SFn nil TAny nil TEMPTY VVoid))
    (in custom ttype at level 3).
Notation "( ) => ret" :=
  (TStructural false (SFn nil TAny nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) TAny nil TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param).
Notation "< x0 > ( ) => ret" :=
  (TStructural false (SFn (cons x0 nil) TAny nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, ret custom ttype at level 3, right associativity).
Notation "< x0 , .. , xn > ( ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny nil TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param).
Notation "< x0 , .. , xn > ( ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, ret custom ttype at level 3, right associativity).
Notation "( y0 ) => 'Void'" :=
  (TStructural false (SFn nil TAny (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2).
Notation "( y0 ) => ret" :=
  (TStructural false (SFn nil TAny (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( y0 ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) TAny (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2).
Notation "< x0 > ( y0 ) => ret" :=
  (TStructural false (SFn (cons x0 nil) TAny (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 , .. , xn > ( y0 ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2).
Notation "< x0 , .. , xn > ( y0 ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( y0 , .. , yn ) => 'Void'" :=
  (TStructural false (SFn nil TAny (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2).
Notation "( y0 , .. , yn ) => ret" :=
  (TStructural false (SFn nil TAny (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( y0 , .. , yn ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) TAny (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2).
Notation "< x0 > ( y0 , .. , yn ) => ret" :=
  (TStructural false (SFn (cons x0 nil) TAny (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "< x0 , .. , xn > ( y0 , .. , yn ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2).
Notation "< x0 , .. , xn > ( y0 , .. , yn ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        ret custom ttype at level 3, right associativity).
Notation "( '___' z ) => 'Void'" :=
  (TStructural false (SFn nil TAny nil z VVoid))
    (in custom ttype at level 3, z custom ttype at level 3).
Notation "( '___' z ) => ret" :=
  (TStructural false (SFn nil TAny nil z (Vt ret)))
    (in custom ttype at level 3, z custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) TAny nil z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, z custom ttype at level 3).
Notation "< x0 > ( '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 nil) TAny nil z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, z custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "< x0 , .. , xn > ( '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny nil z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, z custom ttype at level 3).
Notation "< x0 , .. , xn > ( '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny nil z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity).
Notation "( y0 , '___' z ) => 'Void'" :=
  (TStructural false (SFn nil TAny (cons y0 nil) z VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, z custom ttype at level 3).
Notation "( y0 , '___' z ) => ret" :=
  (TStructural false (SFn nil TAny (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( y0 , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) TAny (cons y0 nil) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3).
Notation "< x0 > ( y0 , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 nil) TAny (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity).
Notation "< x0 , .. , xn > ( y0 , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 nil) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3).
Notation "< x0 , .. , xn > ( y0 , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3,
        ret custom ttype at level 3, right associativity).
Notation "( y0 , .. , yn , '___' z ) => 'Void'" :=
  (TStructural false (SFn nil TAny (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3).
Notation "( y0 , .. , yn , '___' z ) => ret" :=
  (TStructural false (SFn nil TAny (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity).
Notation "< x0 > ( y0 , .. , yn , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) TAny (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3).
Notation "< x0 > ( y0 , .. , yn , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 nil) TAny (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3,
        ret custom ttype at level 3, right associativity).
Notation "< x0 , .. , xn > ( y0 , .. , yn , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        z custom ttype at level 3).
Notation "< x0 , .. , xn > ( y0 , .. , yn , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        z custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "( ( ) => 'Void' )?" :=
  (TStructural true (SFn nil TAny nil TEMPTY VVoid))
    (in custom ttype at level 3).
Notation "( ( ) => ret )?" :=
  (TStructural true (SFn nil TAny nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) TAny nil TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param).
Notation "( < x0 > ( ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) TAny nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, ret custom ttype at level 3, right associativity).
Notation "( < x0 , .. , xn > ( ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny nil TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param).
Notation "( < x0 , .. , xn > ( ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, ret custom ttype at level 3, right associativity).
Notation "( ( y0 ) => 'Void' )?" :=
  (TStructural true (SFn nil TAny (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2).
Notation "( ( y0 ) => ret )?" :=
  (TStructural true (SFn nil TAny (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( y0 ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) TAny (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2).
Notation "( < x0 > ( y0 ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) TAny (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, ret custom ttype at level 3, right associativity).
Notation "( < x0 , .. , xn > ( y0 ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2).
Notation "( < x0 , .. , xn > ( y0 ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( ( y0 , .. , yn ) => 'Void' )?" :=
  (TStructural true (SFn nil TAny (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2).
Notation "( ( y0 , .. , yn ) => ret )?" :=
  (TStructural true (SFn nil TAny (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( y0 , .. , yn ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) TAny (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2).
Notation "( < x0 > ( y0 , .. , yn ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) TAny (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( < x0 , .. , xn > ( y0 , .. , yn ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2).
Notation "( < x0 , .. , xn > ( y0 , .. , yn ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        ret custom ttype at level 3, right associativity).
Notation "( ( '___' z ) => 'Void' )?" :=
  (TStructural true (SFn nil TAny nil z VVoid))
    (in custom ttype at level 3, z custom ttype at level 3).
Notation "( ( '___' z ) => ret )?" :=
  (TStructural true (SFn nil TAny nil z (Vt ret)))
    (in custom ttype at level 3, z custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) TAny nil z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, z custom ttype at level 3).
Notation "( < x0 > ( '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) TAny nil z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, z custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "( < x0 , .. , xn > ( '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny nil z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, z custom ttype at level 3).
Notation "( < x0 , .. , xn > ( '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny nil z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity).
Notation "( ( y0 , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn nil TAny (cons y0 nil) z VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, z custom ttype at level 3).
Notation "( ( y0 , '___' z ) => ret )?" :=
  (TStructural true (SFn nil TAny (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( y0 , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) TAny (cons y0 nil) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3).
Notation "( < x0 > ( y0 , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) TAny (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity).
Notation "( < x0 , .. , xn > ( y0 , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 nil) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3).
Notation "( < x0 , .. , xn > ( y0 , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3,
        ret custom ttype at level 3, right associativity).
Notation "( ( y0 , .. , yn , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn nil TAny (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3).
Notation "( ( y0 , .. , yn , '___' z ) => ret )?" :=
  (TStructural true (SFn nil TAny (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity).
Notation "( < x0 > ( y0 , .. , yn , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) TAny (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3).
Notation "( < x0 > ( y0 , .. , yn , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) TAny (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3,
        ret custom ttype at level 3, right associativity).
Notation "( < x0 , .. , xn > ( y0 , .. , yn , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        z custom ttype at level 3).
Notation "( < x0 , .. , xn > ( y0 , .. , yn , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) TAny (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        z custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "( 'this:' t ) => 'Void'" :=
  (TStructural false (SFn nil t nil TEMPTY VVoid))
    (in custom ttype at level 3, t custom ttype at level 3).
Notation "( 'this:' t ) => ret" :=
  (TStructural false (SFn nil t nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) t nil TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t ) => ret" :=
  (TStructural false (SFn (cons x0 nil) t nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t nil TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( 'this:' t , y0 ) => 'Void'" :=
  (TStructural false (SFn nil t (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, t custom ttype at level 3).
Notation "( 'this:' t , y0 ) => ret" :=
  (TStructural false (SFn nil t (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t , y0 ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) t (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t , y0 ) => ret" :=
  (TStructural false (SFn (cons x0 nil) t (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , y0 ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , y0 ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "( y0 , .. , yn ) => 'Void'" :=
  (TStructural false (SFn nil TAny (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2).
Notation "( y0 , .. , yn ) => ret" :=
  (TStructural false (SFn nil TAny (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( 'this:' t , y0 , .. , yn ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) t (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t , y0 , .. , yn ) => ret" :=
  (TStructural false (SFn (cons x0 nil) t (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , y0 , .. , yn ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , y0 , .. , yn ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( 'this:' t , '___' z ) => 'Void'" :=
  (TStructural false (SFn nil t nil z VVoid))
    (in custom ttype at level 3, z custom ttype at level 3, t custom ttype at level 3).
Notation "( 'this:' t , '___' z ) => ret" :=
  (TStructural false (SFn nil t nil z (Vt ret)))
    (in custom ttype at level 3, z custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) t nil z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, z custom ttype at level 3, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 nil) t nil z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, z custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t nil z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, z custom ttype at level 3, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t nil z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "( 'this:' t , y0 , '___' z ) => 'Void'" :=
  (TStructural false (SFn nil t (cons y0 nil) z VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "( 'this:' t , y0 , '___' z ) => ret" :=
  (TStructural false (SFn nil t (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t , y0 , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) t (cons y0 nil) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t , y0 , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 nil) t (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , y0 , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 nil) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , y0 , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3,
        ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( 'this:' t , y0 , .. , yn , '___' z ) => 'Void'" :=
  (TStructural false (SFn nil t (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "( 'this:' t , y0 , .. , yn , '___' z ) => ret" :=
  (TStructural false (SFn nil t (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t , y0 , .. , yn , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 nil) t (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "< x0 > ( 'this:' t , y0 , .. , yn , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 nil) t (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3,
        ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , y0 , .. , yn , '___' z ) => 'Void'" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        z custom ttype at level 3, t custom ttype at level 3).
Notation "< x0 , .. , xn > ( 'this:' t , y0 , .. , yn , '___' z ) => ret" :=
  (TStructural false (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        z custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( ( 'this:' t ) => 'Void' )?" :=
  (TStructural true (SFn nil t nil TEMPTY VVoid))
    (in custom ttype at level 3, t custom ttype at level 3).
Notation "( ( 'this:' t ) => ret )?" :=
  (TStructural true (SFn nil t nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) t nil TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) t nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t nil TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t nil TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( ( 'this:' t , y0 ) => 'Void' )?" :=
  (TStructural true (SFn nil t (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, t custom ttype at level 3).
Notation "( ( 'this:' t , y0 ) => ret )?" :=
  (TStructural true (SFn nil t (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , y0 ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) t (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , y0 ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) t (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , y0 ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 nil) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , y0 ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 nil) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "( ( 'this:' t , y0 , .. , yn ) => 'Void' )?" :=
  (TStructural true (SFn nil t (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, t custom ttype at level 3).
Notation "( ( 'this:' t , y0 , .. , yn ) => ret )?" :=
  (TStructural true (SFn nil t (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , y0 , .. , yn ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) t (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , y0 , .. , yn ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) t (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , y0 , .. , yn ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 .. (cons yn nil) .. ) TEMPTY VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , y0 , .. , yn ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 .. (cons yn nil) .. ) TEMPTY (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( ( 'this:' t , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn nil t nil z VVoid))
    (in custom ttype at level 3, z custom ttype at level 3, t custom ttype at level 3).
Notation "( ( 'this:' t , '___' z ) => ret )?" :=
  (TStructural true (SFn nil t nil z (Vt ret)))
    (in custom ttype at level 3, z custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) t nil z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, z custom ttype at level 3, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) t nil z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, z custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t nil z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, z custom ttype at level 3, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t nil z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "( ( 'this:' t , y0 , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn nil t (cons y0 nil) z VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "( ( 'this:' t , y0 , '___' z ) => ret )?" :=
  (TStructural true (SFn nil t (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , y0 , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) t (cons y0 nil) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , y0 , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) t (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , y0 , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 nil) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , y0 , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 nil) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, z custom ttype at level 3,
        ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( ( 'this:' t , y0 , .. , yn , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn nil t (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "( ( 'this:' t , y0 , .. , yn , '___' z ) => ret )?" :=
  (TStructural true (SFn nil t (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3, ret custom ttype at level 3,
        right associativity, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , y0 , .. , yn , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 nil) t (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3, t custom ttype at level 3).
Notation "( < x0 > ( 'this:' t , y0 , .. , yn , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 nil) t (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2, z custom ttype at level 3,
        ret custom ttype at level 3, right associativity, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , y0 , .. , yn , '___' z ) => 'Void' )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 .. (cons yn nil) .. ) z VVoid))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        z custom ttype at level 3, t custom ttype at level 3).
Notation "( < x0 , .. , xn > ( 'this:' t , y0 , .. , yn , '___' z ) => ret )?" :=
  (TStructural true (SFn (cons x0 .. (cons xn nil) .. ) t (cons y0 .. (cons yn nil) .. ) z (Vt ret)))
    (in custom ttype at level 3, x0 custom ttype_param, xn custom ttype_param, y0 custom ottype at level 2, yn custom ottype at level 2,
        z custom ttype at level 3, ret custom ttype at level 3, right associativity, t custom ttype at level 3).
(* Unfortunately coq doesn't let us quote strings directly, because usually it shallow embeds the binders / ids *)
Notation "x" := x (in custom ttype_ident at level 0, x global).
Notation "x" := (TParam Bivariant x nil) (in custom ttype_param at level 0, x custom ttype_ident).
Notation "'biv' x" := (TParam Bivariant x nil) (in custom ttype_param at level 0, x custom ttype_ident).
Notation "'inv' x" := (TParam Invariant x nil) (in custom ttype_param at level 0, x custom ttype_ident).
Notation "'cov' x" := (TParam Covariant x nil) (in custom ttype_param at level 0, x custom ttype_ident).
Notation "'con' x" := (TParam Contravariant x nil) (in custom ttype_param at level 0, x custom ttype_ident).
Notation "x <: y0" := (TParam Bivariant x (cons y0 nil)) (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3).
Notation "'biv' x <: y0" := (TParam Bivariant x (cons y0 nil)) (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3).
Notation "'inv' x <: y0" := (TParam Invariant x (cons y0 nil)) (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3).
Notation "'cov' x <: y0" := (TParam Covariant x (cons y0 nil)) (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3).
Notation "'con' x <: y0" := (TParam Contravariant x (cons y0 nil)) (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3).
Notation "x <: y0 & .. & yn" :=
  (TParam Bivariant x (cons y0 .. (cons yn nil) .. ))
    (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3, yn custom ttype at level 3).
Notation "'biv' x <: y0 & .. & yn" :=
  (TParam Bivariant x (cons y0 .. (cons yn nil) .. ))
    (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3, yn custom ttype at level 3).
Notation "'inv' x <: y0 & .. & yn" :=
  (TParam Invariant x (cons y0 .. (cons yn nil) .. ))
    (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3, yn custom ttype at level 3).
Notation "'cov' x <: y0 & .. & yn" :=
  (TParam Covariant x (cons y0 .. (cons yn nil) .. ))
    (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3, yn custom ttype at level 3).
Notation "'con' x <: y0 & .. & yn" :=
  (TParam Contravariant x (cons y0 .. (cons yn nil) .. ))
    (in custom ttype_param at level 0, x custom ttype_ident, y0 custom ttype at level 3, yn custom ttype at level 3).
Notation "x" := (O false x) (in custom ottype at level 0, x custom ttype at level 2).
Notation "? x" := (O true x) (in custom ottype at level 0, x custom ttype at level 2).
Notation "name : value" := (name, O false value) (in custom ttype_field at level 0, name custom ttype_ident, value custom ttype at level 3).
Notation "name ?: value" := (name, O true value) (in custom ttype_field at level 0, name custom ttype_ident, value custom ttype at level 3).
Example Integer := "Integer"%string.
Example Natural := "Natural"%string.
Example String := "String"%string.
Example test0: ttype := [! Natural !].
Example test1: ttype := let Foo := "Foo"%string in [! Foo !].
Example test2: ttype := let Bar := "Bar"%string in [! Bar<Natural> !].
Example test3: ttype := let Baz := "Baz"%string in [! Baz<String, Natural> !].
Example test4: ttype := [! String [] !].
Example test5: ttype := let Foo := "Foo"%string in let Bar := "Bar"%string in let Baz := "Baz"%string in [! [Foo, Bar, Baz] !].
Example test6: ttype := let Foo := "Foo"%string in let Bar := "Bar"%string in let Baz := "Baz"%string in [! [Foo, Bar, Baz] [] !].
Example test7: ttype := let Foo := "Foo"%string in let Bar := "Bar"%string in let Baz := "Baz"%string in
                        let foo := "foo"%string in let bar := "bar"%string in let baz := "baz"%string in
                        [! { foo : Foo, bar : [ Bar ], baz : Baz <String> [] } [] !].
(* Coq can either allow () or (  ), but not both unless we explicitly define both (same for brackets and braces) *)
Example test8: ttype := [! ( ) => Void !].
Example test9: ttype := [! ( Integer , ___ Integer) => String? !].
Example test10: ttype := let Foo := "Foo"%string in let foo := "foo"%string in
                         [! ( <Foo>(Natural[], { foo : Foo<String> }) => (Integer) => String[][] )? !].

Example test11: ttype := [! (? Integer) => String? !].
Example test12: ttype := let Foo := "Foo"%string in let foo := "foo"%string in
                         [! ( <inv Foo <: Foo>(Natural[], ? { foo ?: Foo<[? String ]> }) => (Integer) => String[][] )? !].
Example test13: ttype := let Foo := "Foo"%string in let foo := "foo"%string in
                         [! ( <inv Foo <: ( ) => Void & Foo>(Natural[], ? { foo ?: Foo<[? String ]> }) => (Integer) => String[][] )? !].
Example test14: ttype := let Foo := "Foo"%string in let foo := "foo"%string in
                         [! ( <inv Foo <: Foo>(this: Natural[], ? { foo ?: Foo<[? String ]> }) => ( ___ Integer) => String[][] )? !].
