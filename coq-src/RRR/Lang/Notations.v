Require Import Lang.Syntax.

(* Notations borrowed from https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/notation.v *)

Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Notation "V@0" := (val_var VZ) (only parsing)
  (* (at level 60, V at level 55, only parsing)  *)
  : expr_scope.
Notation "V@1" := (val_var (VS VZ)) (only parsing): expr_scope.
Notation "V@2" := (val_var (VS (VS VZ))) (only parsing): expr_scope.
Notation "V@3" := (val_var (VS (VS (VS VZ)))) (only parsing): expr_scope.
Notation "V@4" := (val_var (VS (VS (VS (VS VZ))))) (only parsing): expr_scope.
Notation "V@5" := (val_var (VS (VS (VS (VS (VS VZ)))))) (only parsing): expr_scope.

Notation "'()'" := val_unit (only parsing) : expr_scope.

Notation "'TRUE'" := (val_bool true) (only parsing) : expr_scope.
Notation "'FALSE'" := (val_bool false) (only parsing) : expr_scope.
Notation "'Const' r" := (val_real r) (at level 60, only parsing) : expr_scope.

Notation "λ: e" := (val_fun e%E)
  (at level 200, e at level 200, only parsing) : expr_scope.

Notation "fix: e" := (val_fix e%E)
  (at level 200, e at level 200, only parsing) : expr_scope.

Coercion exp_app : exp >-> Funclass.

Notation "'let:' e1 'in' e2" := (exp_let e1%E e2%E)
  (at level 200, e1, e2 at level 200, only parsing) : expr_scope.

Notation "e1 + e2" := (exp_binop binop_plus e1%E e2%E) (only parsing) : expr_scope.
Notation "e1 * e2" := (exp_binop binop_mult e1%E e2%E) (only parsing) : expr_scope.
Notation "e1 < e2" := (exp_binop binop_lt e1%E e2%E) (only parsing) : expr_scope.
Notation "e1 ≤ e2" := (exp_binop binop_le e1%E e2%E) (only parsing) : expr_scope.
Notation "e1 = e2" := (exp_binop binop_eq_real e1%E e2%E) (only parsing) : expr_scope.

Notation "'fst' e" := (exp_proj e%E true)
  (at level 200, e at level 200, only parsing) : expr_scope.
Notation "'snd' e" := (exp_proj e false)
  (at level 200, e at level 200, only parsing) : expr_scope.

Notation "'if:' cond 'then' t_branch 'else' f_branch" := (exp_if cond%E t_branch%E f_branch%E)
  (at level 200, cond, t_branch, f_branch at level 200, only parsing) : expr_scope.

Notation query := val_query (only parsing).
Notation sample := exp_sample (only parsing).
Notation score := exp_score (only parsing).
Notation exn := exp_exn (only parsing).
