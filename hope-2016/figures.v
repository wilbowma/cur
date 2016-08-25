(* source https://github.com/eholk/coq-stlc/blob/master/Stlc.v *)

Inductive Expr :=
| Unit : Expr
| Var : Symbol -> Expr
| Pair : Expr -> Expr -> Expr
| Fst : Expr -> Expr
| Snd : Expr -> Expr
| Lambda : Symbol -> Expr -> Expr
| App : Expr -> Expr -> Expr.

Inductive StlcType :=
| TUnit : StlcType
| TPair : StlcType -> StlcType -> StlcType
| Fn : StlcType -> StlcType -> StlcType.


Inductive Env Val :=
| EmptyEnv : Env Val
| ExtendEnv : Symbol -> Val -> Env Val -> Env Val.

(* There are two values: units and closures. *)
Inductive Value :=
| VUnit : Value
| Closure : Symbol -> Expr -> (Env Value) -> Value.

(* The two values correspond to two types, one for units and another
for closures. *)
