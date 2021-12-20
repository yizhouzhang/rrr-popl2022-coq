Require Import Lang.Syntax.

Set Implicit Arguments.
Implicit Types V : Set.

(** If we can change the representation of a variable from [A] to [B],
then we can change the representation of a variable from [inc A] to
[inc B]. *)
Definition map_inc V1 V2 (f : V1 → V2) : inc V1 → inc V2 :=
  λ v, match v with
  | VZ    => VZ
  | VS v' => VS (f v')
  end.

(** Change the variable representation type [V] to [V']. *)
Fixpoint V_map_val
V V' (f : V → V')
(v : val V) {struct v} : val V' :=
match v with
| val_var x => val_var (f x)
| val_unit => val_unit
| val_bool b => val_bool b
| val_real r => val_real r
| val_fun e => val_fun (V_map_exp (map_inc f) e)
| val_fix e => val_fix (V_map_exp (map_inc f) e)
| val_pair v1 v2 => val_pair (V_map_val f v1) (V_map_val f v2)
| val_unif => val_unif
| val_query e => val_query (V_map_exp f e)
end
with V_map_exp
V V' (f : V → V')
(e : exp V) {struct e} : exp V' :=
match e with
| exp_val v => exp_val (V_map_val f v)
| exp_app e1 e2 => exp_app (V_map_exp f e1) (V_map_exp f e2)
| exp_let e1 e2 => exp_let (V_map_exp f e1) (V_map_exp (map_inc f) e2)
| exp_binop op e1 e2 => exp_binop op (V_map_exp f e1) (V_map_exp f e2)
| exp_proj e b => exp_proj (V_map_exp f e) b
| exp_if e1 e2 e3 => exp_if (V_map_exp f e1) (V_map_exp f e2) (V_map_exp f e3)
| exp_sample e => exp_sample (V_map_exp f e)
| exp_score e => exp_score (V_map_exp f e)
| exp_exn => exp_exn
end
.

Notation V_shift_val := (V_map_val (@VS _)).
Notation V_shift_exp := (V_map_exp (@VS _)).

(** Syntactic objects that do not contain free variables can be used
in any context that binds free variables. *)
Notation V_open_val := (V_map_val ∅→).
Notation V_open_exp := (V_map_exp ∅→).


(** If we have a substitution function of form [V → val V'],
then we can turn it into one of form [inc V → val (inc V')]. *)
Definition V_lift_inc V V' (f : V → val V') : inc V → val (inc V') :=
λ x, match x with
| VZ   => val_var VZ
| VS β => V_shift_val (f β)
end.

(** Apply the substitution function [f : V → val V'] *)
Fixpoint V_bind_val
V V' (f : V → val V')
(v : val V) {struct v} : val V' :=
match v with
| val_var x => f x
| val_unit => val_unit
| val_bool b => val_bool b
| val_real r => val_real r
| val_fun e => val_fun (V_bind_exp (V_lift_inc f) e)
| val_fix e => val_fix (V_bind_exp (V_lift_inc f) e)
| val_pair v1 v2 => val_pair (V_bind_val f v1) (V_bind_val f v2)
| val_unif => val_unif
| val_query e => val_query (V_bind_exp f e)
end
with V_bind_exp
V V' (f : V → val V')
(e : exp V) {struct e} : exp V' :=
match e with
| exp_val v => exp_val (V_bind_val f v)
| exp_app e1 e2 => exp_app (V_bind_exp f e1) (V_bind_exp f e2)
| exp_let e1 e2 => exp_let (V_bind_exp f e1) (V_bind_exp (V_lift_inc f) e2)
| exp_binop op e1 e2 => exp_binop op (V_bind_exp f e1) (V_bind_exp f e2)
| exp_proj e b => exp_proj (V_bind_exp f e) b
| exp_if e1 e2 e3 => exp_if (V_bind_exp f e1) (V_bind_exp f e2) (V_bind_exp f e3)
| exp_sample e => exp_sample (V_bind_exp f e)
| exp_score e => exp_score (V_bind_exp f e)
| exp_exn => exp_exn
end
.

(** Substitution functions for one free variable. *)
Definition V_substfun V (v : val V) : inc V → val V :=
λ x, match x with
| VZ   => v
| VS y => val_var y
end.

(** Substitution functions for one free variable. Innermost bound variable is
substituted by [v2]. *)
Definition V2_substfun V (v1 v2 : val V) : inc (inc V) → val V :=
λ x, match x with
| VZ        => v2
| VS VZ     => v1
| VS (VS y) => val_var y
end.

Notation V_subst_val v := (V_bind_val (V_substfun v)).
Notation V_subst_exp v := (V_bind_exp (V_substfun v)).
