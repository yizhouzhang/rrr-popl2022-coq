Require Import Lang.Syntax.
Require Import Lang.Bindings.

Set Implicit Arguments.
Implicit Types V : Set.

Definition binop_ty (op : binop) : ty :=
match op with
| binop_plus => ty_real
| binop_mult => ty_real
| binop_lt => ty_bool
| binop_le => ty_bool
| binop_eq_real => ty_bool
end.

Inductive wf_val V (Γ : V → ty) : val V → ty → Prop :=
| wf_val_var : ∀ x, wf_val Γ (val_var x) (Γ x)
| wf_val_real : ∀ r, wf_val Γ (val_real r) ty_real
| wf_val_unit : wf_val Γ val_unit ty_unit
| wf_val_bool : ∀ b, wf_val Γ (val_bool b) ty_bool
| wf_val_fun :
  ∀ e T1 T2, wf_exp (V := inc V) (env_ext Γ T1) e T2 →
  wf_val Γ (val_fun e) (ty_fun T1 T2)
| wf_val_fix :
  ∀ e T, wf_exp (V := inc V) (env_ext Γ (ty_fun ty_unit T)) e T →
  wf_val Γ (val_fix e) (ty_fun ty_unit T)
| wf_val_pair :
  ∀ vL vR TL TR,
  wf_val Γ vL TL → wf_val Γ vR TR →
  wf_val Γ (val_pair vL vR) (ty_pair TL TR)
| wf_val_unif : wf_val Γ val_unif (ty_dist ty_real)
| wf_val_query :
  ∀ e T,
  wf_exp Γ e T → T = ℝ ∨ T = ty_bool →
  wf_val Γ (val_query e) (ty_dist T)
with wf_exp V (Γ : V → ty) : exp V → ty → Prop :=
| wf_exp_val : ∀ v T, wf_val Γ v T → wf_exp Γ v T
| wf_exp_app :
  ∀ e1 e2 T1 T2,
  wf_exp Γ e1 (ty_fun T1 T2) → wf_exp Γ e2 T1 →
  wf_exp Γ (exp_app e1 e2) T2
| wf_exp_let :
  ∀ e1 e2 T1 T2,
  wf_exp Γ e1 T1 → wf_exp (V := inc V) (env_ext Γ T1) e2 T2 →
  wf_exp Γ (exp_let e1 e2) T2
| wf_exp_binop :
  ∀ op e1 e2 ,
  wf_exp Γ e1 ty_real → wf_exp Γ e2 ty_real →
  wf_exp Γ (exp_binop op e1 e2) (binop_ty op)
| wf_exp_proj :
  ∀ e b TL TR,
  wf_exp Γ e (ty_pair TL TR) →
  wf_exp Γ (exp_proj e b) (if b then TL else TR)
| wf_exp_if :
  ∀ e1 e2 e3 T,
  wf_exp Γ e1 ty_bool → wf_exp Γ e2 T → wf_exp Γ e3 T →
  wf_exp Γ (exp_if e1 e2 e3) T
| wf_exp_sample :
  ∀ e T,
  wf_exp Γ e (ty_dist T) →
  wf_exp Γ (exp_sample e) T
| wf_exp_score :
  ∀ e,
  wf_exp Γ e ty_real →
  wf_exp Γ (exp_score e) ty_unit
| wf_exp_exn :
  ∀ T,
  wf_exp Γ exp_exn T
.

Definition wf_env V (γ : V → val0) (Γ : V → ty) : Prop :=
∀ (v : V), wf_val ∅→ (γ v) (Γ v).