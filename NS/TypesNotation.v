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
Notation "[! x !]" := x (x custom ttype) : ttype_scope.
Notation "( x )" := x (in custom ttype, x custom ttype).
Notation "{! x !}" := x (in custom ttype, x constr).
Notation "'Any'" := AAny (in custom ttype).
Notation "'Never'" := (AType false NNever) (in custom ttype).
Notation "'Null'" := (AType true NNever) (in custom ttype).
Notation "x" := (AType false (NType (TTypeNominal (IType x nil)))) (in custom ttype at level 0, x custom ttype_ident).
Notation "x ?" := (AType true (NType (TTypeNominal (IType x nil)))) (in custom ttype at level 0, x custom ttype_ident).
Notation "x < x0 >" :=
  (AType false (NType (TTypeNominal (IType x (cons x0 nil)))))
    (in custom ttype at level 0, x custom ttype_ident, x0 custom ttype at level 3).
Notation "x < x0 > ?" :=
  (AType true (NType (TTypeNominal (IType x (cons x0 nil)))))
    (in custom ttype at level 0, x custom ttype_ident, x0 custom ttype at level 3).
Notation "x < x0 , .. , xn >" :=
  (AType false (NType (TTypeNominal (IType x (cons x0 .. (cons xn nil) .. )))))
    (in custom ttype at level 0, x custom ttype_ident, x0 custom ttype at level 3, xn custom ttype at level 3).
Notation "x < x0 , .. , xn > ?" :=
  (AType true (NType (TTypeNominal (IType x (cons x0 .. (cons xn nil) .. )))))
    (in custom ttype at level 0, x custom ttype_ident, x0 custom ttype at level 3, xn custom ttype at level 3).
Notation "x []" := (AType false (NType (TTypeStructural (SArray x)))) (in custom ttype at level 2, x custom ttype).
Notation "x [] ?" := (AType true (NType (TTypeStructural (SArray x)))) (in custom ttype at level 2, x custom ttype).
Notation "[ ]" := (AType false (NType (TTypeStructural (STuple nil)))) (in custom ttype).
Notation "[ ] ?" := (AType true (NType (TTypeStructural (STuple nil)))) (in custom ttype).
Notation "[ x0 ]" := (AType false (NType (TTypeStructural (STuple (cons x0 nil))))) (in custom ttype, x0 custom ttype at level 3).
Notation "[ x0 ] ?" := (AType true (NType (TTypeStructural (STuple (cons x0 nil))))) (in custom ttype, x0 custom ttype at level 3).
Notation "[ x0 , .. , xn ]" :=
  (AType false (NType (TTypeStructural (STuple (cons x0 .. (cons xn nil) .. )))))
    (in custom ttype, x0 custom ttype at level 3, xn custom ttype at level 3).
Notation "[ x0 , .. , xn ] ?" :=
  (AType true (NType (TTypeStructural (STuple (cons x0 .. (cons xn nil) .. )))))
    (in custom ttype, x0 custom ttype at level 3, xn custom ttype at level 3).
Notation "{ }" := (AType false (NType (TTypeStructural (SObject nil)))) (in custom ttype).
Notation "{ } ?" := (AType true (NType (TTypeStructural (SObject nil)))) (in custom ttype).
Notation "{ x0 }" := (AType false (NType (TTypeStructural (SObject (cons x0 nil))))) (in custom ttype, x0 custom ttype_field).
Notation "{ x0 } ?" := (AType true (NType (TTypeStructural (SObject (cons x0 nil))))) (in custom ttype, x0 custom ttype_field).
Notation "{ x0 , .. , xn }" :=
  (AType false (NType (TTypeStructural (SObject (cons x0 .. (cons xn nil) .. )))))
    (in custom ttype, x0 custom ttype_field, xn custom ttype_field).
Notation "{ x0 , .. , xn } ?" :=
  (AType true (NType (TTypeStructural (SObject (cons x0 .. (cons xn nil) .. )))))
    (in custom ttype, x0 custom ttype_field, xn custom ttype_field).
Notation "name : value" := (name, value) (in custom ttype_field at level 0, name custom ttype_ident, value custom ttype at level 3).
(* There are a *lot* of overloads for function types,
   because we need to define 3 variants for varargs (of which there are 2),
   2 variants for optional args, and 2 variants for "Void" or regular return value (though could define another custom entry here.)
   3 * 3 * 2 * 2 = 36, so we have 36 notations. At least none of them can be nullable without parenthesis... *)
Notation "( ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn nil nil None VVoid))))
    (in custom ttype at level 3).
Notation "( ) => ret" :=
  (AType false (NType (TTypeStructural (SFn nil nil None (VType ret)))))
    (in custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) nil None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident).
Notation "< x0 > ( ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) nil None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, ret custom ttype at level 3, right associativity).
Notation "< x0 , .. , xn > ( ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) nil None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident).
Notation "< x0 , .. , xn > ( ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) nil None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, ret custom ttype at level 3, right associativity).
Notation "( y0 ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn nil (cons y0 nil) None VVoid))))
    (in custom ttype at level 3, y0 custom ttype at level 2).
Notation "( y0 ) => ret" :=
  (AType false (NType (TTypeStructural (SFn nil (cons y0 nil) None (VType ret)))))
    (in custom ttype at level 3, y0 custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( y0 ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 nil) None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2).
Notation "< x0 > ( y0 ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 nil) None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 , .. , xn > ( y0 ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 nil) None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2).
Notation "< x0 , .. , xn > ( y0 ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 nil) None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( y0 , .. , yn ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn nil (cons y0 .. (cons yn nil) .. ) None VVoid))))
    (in custom ttype at level 3, y0 custom ttype at level 2, yn custom ttype at level 2).
Notation "( y0 , .. , yn ) => ret" :=
  (AType false (NType (TTypeStructural (SFn nil (cons y0 .. (cons yn nil) .. ) None (VType ret)))))
    (in custom ttype at level 3, y0 custom ttype at level 2, yn custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( y0 , .. , yn ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 .. (cons yn nil) .. ) None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2).
Notation "< x0 > ( y0 , .. , yn ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 .. (cons yn nil) .. ) None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "< x0 , .. , xn > ( y0 , .. , yn ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 .. (cons yn nil) .. ) None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2).
Notation "< x0 , .. , xn > ( y0 , .. , yn ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 .. (cons yn nil) .. ) None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2,
        ret custom ttype at level 3, right associativity).
Notation "( '...' z ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn nil nil (Some z) VVoid))))
    (in custom ttype at level 3, z custom ttype at level 2).
Notation "( '...' z ) => ret" :=
  (AType false (NType (TTypeStructural (SFn nil nil (Some z) (VType ret)))))
    (in custom ttype at level 3, z custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( '...' z ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) nil (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, z custom ttype at level 2).
Notation "< x0 > ( '...' z ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) nil (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, z custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 , .. , xn > ( '...' z ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) nil (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, z custom ttype at level 2).
Notation "< x0 , .. , xn > ( '...' z ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) nil (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, z custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( y0 , '...' z ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn nil (cons y0 nil) (Some z) VVoid))))
    (in custom ttype at level 3, y0 custom ttype at level 2, z custom ttype at level 2).
Notation "( y0 , '...' z ) => ret" :=
  (AType false (NType (TTypeStructural (SFn nil (cons y0 nil) (Some z) (VType ret)))))
    (in custom ttype at level 3, y0 custom ttype at level 2, z custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "< x0 > ( y0 , '...' z ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 nil) (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, z custom ttype at level 2).
Notation "< x0 > ( y0 , '...' z ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 nil) (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, z custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "< x0 , .. , xn > ( y0 , '...' z ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 nil) (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, z custom ttype at level 2).
Notation "< x0 , .. , xn > ( y0 , '...' z ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 nil) (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, z custom ttype at level 2,
        ret custom ttype at level 3, right associativity).
Notation "( y0 , .. , yn , '...' z ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn nil (cons y0 .. (cons yn nil) .. ) (Some z) VVoid))))
    (in custom ttype at level 3, y0 custom ttype at level 2, yn custom ttype at level 2, z custom ttype at level 2).
Notation "( y0 , .. , yn , '...' z ) => ret" :=
  (AType false (NType (TTypeStructural (SFn nil (cons y0 .. (cons yn nil) .. ) (Some z) (VType ret)))))
    (in custom ttype at level 3, y0 custom ttype at level 2, yn custom ttype at level 2, z custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "< x0 > ( y0 , .. , yn , '...' z ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 .. (cons yn nil) .. ) (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2, z custom ttype at level 2).
Notation "< x0 > ( y0 , .. , yn , '...' z ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 .. (cons yn nil) .. ) (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2, z custom ttype at level 2,
        ret custom ttype at level 3, right associativity).
Notation "< x0 , .. , xn > ( y0 , .. , yn , '...' z ) => 'Void'" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 .. (cons yn nil) .. ) (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2,
        z custom ttype at level 2).
Notation "< x0 , .. , xn > ( y0 , .. , yn , '...' z ) => ret" :=
  (AType false (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 .. (cons yn nil) .. ) (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2,
        z custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "( ( ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn nil nil None VVoid))))
    (in custom ttype at level 3).
Notation "( ( ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn nil nil None (VType ret)))))
    (in custom ttype at level 3, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) nil None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident).
Notation "( < x0 > ( ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) nil None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, ret custom ttype at level 3, right associativity).
Notation "( < x0 , .. , xn > ( ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) nil None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident).
Notation "( < x0 , .. , xn > ( ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) nil None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, ret custom ttype at level 3, right associativity).
Notation "( ( y0 ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn nil (cons y0 nil) None VVoid))))
    (in custom ttype at level 3, y0 custom ttype at level 2).
Notation "( ( y0 ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn nil (cons y0 nil) None (VType ret)))))
    (in custom ttype at level 3, y0 custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( y0 ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 nil) None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2).
Notation "( < x0 > ( y0 ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 nil) None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "( < x0 , .. , xn > ( y0 ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 nil) None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2).
Notation "( < x0 , .. , xn > ( y0 ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 nil) None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( ( y0 , .. , yn ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn nil (cons y0 .. (cons yn nil) .. ) None VVoid))))
    (in custom ttype at level 3, y0 custom ttype at level 2, yn custom ttype at level 2).
Notation "( ( y0 , .. , yn ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn nil (cons y0 .. (cons yn nil) .. ) None (VType ret)))))
    (in custom ttype at level 3, y0 custom ttype at level 2, yn custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( y0 , .. , yn ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 .. (cons yn nil) .. ) None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2).
Notation "( < x0 > ( y0 , .. , yn ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 .. (cons yn nil) .. ) None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( < x0 , .. , xn > ( y0 , .. , yn ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 .. (cons yn nil) .. ) None VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2).
Notation "( < x0 , .. , xn > ( y0 , .. , yn ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 .. (cons yn nil) .. ) None (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2,
        ret custom ttype at level 3, right associativity).
Notation "( ( '...' z ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn nil nil (Some z) VVoid))))
    (in custom ttype at level 3, z custom ttype at level 2).
Notation "( ( '...' z ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn nil nil (Some z) (VType ret)))))
    (in custom ttype at level 3, z custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( '...' z ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) nil (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, z custom ttype at level 2).
Notation "( < x0 > ( '...' z ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) nil (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, z custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "( < x0 , .. , xn > ( '...' z ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) nil (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, z custom ttype at level 2).
Notation "( < x0 , .. , xn > ( '...' z ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) nil (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, z custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( ( y0 , '...' z ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn nil (cons y0 nil) (Some z) VVoid))))
    (in custom ttype at level 3, y0 custom ttype at level 2, z custom ttype at level 2).
Notation "( ( y0 , '...' z ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn nil (cons y0 nil) (Some z) (VType ret)))))
    (in custom ttype at level 3, y0 custom ttype at level 2, z custom ttype at level 2, ret custom ttype at level 3, right associativity).
Notation "( < x0 > ( y0 , '...' z ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 nil) (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, z custom ttype at level 2).
Notation "( < x0 > ( y0 , '...' z ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 nil) (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, z custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( < x0 , .. , xn > ( y0 , '...' z ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 nil) (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, z custom ttype at level 2).
Notation "( < x0 , .. , xn > ( y0 , '...' z ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 nil) (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, z custom ttype at level 2,
        ret custom ttype at level 3, right associativity).
Notation "( ( y0 , .. , yn , '...' z ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn nil (cons y0 .. (cons yn nil) .. ) (Some z) VVoid))))
    (in custom ttype at level 3, y0 custom ttype at level 2, yn custom ttype at level 2, z custom ttype at level 2).
Notation "( ( y0 , .. , yn , '...' z ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn nil (cons y0 .. (cons yn nil) .. ) (Some z) (VType ret)))))
    (in custom ttype at level 3, y0 custom ttype at level 2, yn custom ttype at level 2, z custom ttype at level 2, ret custom ttype at level 3,
        right associativity).
Notation "( < x0 > ( y0 , .. , yn , '...' z ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 .. (cons yn nil) .. ) (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2, z custom ttype at level 2).
Notation "( < x0 > ( y0 , .. , yn , '...' z ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 nil) (cons y0 .. (cons yn nil) .. ) (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2, z custom ttype at level 2,
        ret custom ttype at level 3, right associativity).
Notation "( < x0 , .. , xn > ( y0 , .. , yn , '...' z ) => 'Void' )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 .. (cons yn nil) .. ) (Some z) VVoid))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2,
        z custom ttype at level 2).
Notation "( < x0 , .. , xn > ( y0 , .. , yn , '...' z ) => ret )?" :=
  (AType true (NType (TTypeStructural (SFn (cons x0 .. (cons xn nil) .. ) (cons y0 .. (cons yn nil) .. ) (Some z) (VType ret)))))
    (in custom ttype at level 3, x0 custom ttype_ident, xn custom ttype_ident, y0 custom ttype at level 2, yn custom ttype at level 2,
        z custom ttype at level 2, ret custom ttype at level 3, right associativity).
(* Unfortunately coq doesn't let us quote strings directly, because usually it shallow embeds the binders / ids *)
Notation "x" := x (in custom ttype_ident at level 0, x global).
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
Example test9: ttype := [! (Integer) => String? !].
Example test10: ttype := let Foo := "Foo"%string in let foo := "foo"%string in
                         [! ( <Foo>(Natural[], { foo : Foo<String> }) => (Integer) => String[][] )? !].
