Require Import Utf8 List Basics Reals.
Import ListNotations.

Require Export Utf8 List Basics Reals.
Export ListNotations.
Require Export CpdtTactics.

Open Scope program_scope.

Set Implicit Arguments.
Implicit Types V : Set.

(** * Syntax *)

(**
If [V] is the type of the representation of a variable, then [inc V]
is the type of the representation of the same variable after the free
variable environment is extended by one.
*)
Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.

Arguments VZ {V}.
Arguments VS {V}.

Notation "∅" := Empty_set.

Definition empty_fun {T} : ∅ → T :=
  λ y, match y with end.

Notation "∅→" := empty_fun.

(** Extend a variable mapping. *)
Definition env_ext (V : Set) (T : Type) (env : V → T) (t : T) :
    inc V → T :=
  λ y, match y with
  | VZ => t
  | VS x => env x
  end.

(** types *)
Inductive ty : Set :=
| ty_unit : ty
| ty_bool : ty
| ty_real : ty
| ty_fun  : ty → ty → ty
| ty_pair : ty → ty → ty
| ty_dist : ty → ty
.
Notation "𝟙" := ty_unit.
Notation "𝟚" := ty_bool.
Notation ℝ := ty_real.
Notation 𝕋 := ty.

Inductive binop : Set :=
(** binary operations *)
| binop_plus
| binop_mult
| binop_lt
| binop_le
| binop_eq_real
.

Inductive val V : Set :=
(** values *)
| val_var   : V → val V
| val_unit  : val V
| val_bool  : bool → val V
| val_real  : R → val V
| val_fun   : exp (inc V) → val V
| val_fix   : exp (inc V) → val V
| val_pair  : val V → val V → val V
| val_unif  : val V
| val_query : exp V → val V

with exp V : Set :=
(** terms *)
| exp_val     : val V → exp V
| exp_app     : exp V → exp V → exp V
| exp_let     : exp V → exp (inc V) → exp V
| exp_binop   : binop → exp V → exp V → exp V
| exp_proj    : exp V → bool → exp V
| exp_if      : exp V → exp V → exp V → exp V
| exp_sample  : exp V → exp V
| exp_score   : exp V → exp V
| exp_exn     : exp V
.

Arguments val_unit {V}.
Arguments val_bool {V}.
Arguments val_real {V}.
Arguments val_unif {V}.
Arguments exp_exn {V}.

Notation val0 := (val ∅).
Notation exp0 := (exp ∅).

Coercion exp_val : val >-> exp.

Inductive ktx : Set :=
(** evaluation contexts *)
| ktx_hole   : ktx
| ktx_app1   : ktx → exp0 → ktx
| ktx_app2   : val0 → ktx → ktx
| ktx_let    : ktx → exp (inc ∅) → ktx
| ktx_binop1 : binop → ktx → exp0 → ktx
| ktx_binop2 : binop → val0 → ktx → ktx
| ktx_proj   : ktx → bool → ktx
| ktx_if     : ktx → exp0 → exp0 → ktx
| ktx_sample : ktx → ktx
| ktx_score  : ktx → ktx
.

(** Well-founded measure on the syntax *)
Fixpoint size_val
V (v : val V) : nat := 
match v with
| val_var _ => 0
| val_unit => 0
| val_bool _ => 0
| val_real _ => 0
| val_fun e => 1 + size_exp e
| val_fix e => 1 + size_exp e
| val_pair v1 v2 => 1 + size_val v1 + size_val v2
| val_unif => 0
| val_query e => 1 + size_exp e
end
with size_exp
V (e : exp V) : nat := 
match e with
| exp_val v => 1 + size_val v
| exp_app e1 e2 => 1 + size_exp e1 + size_exp e2
| exp_let e1 e2 => 1 + size_exp e1 + size_exp e2
| exp_binop _ e1 e2 => 1 + size_exp e1 + size_exp e2
| exp_proj e1 _ => 1 + size_exp e1
| exp_if e1 e2 e3 => 1 + size_exp e1 + size_exp e2 + size_exp e3
| exp_sample e => 1 + size_exp e
| exp_score e => 1 + size_exp e
| exp_exn => 0
end.



Reserved Notation "K '[/' e ']'" (at level 60, e at level 55).
Fixpoint ktx_plug (K : ktx) (e : exp0) {struct K} :=
match K with
| ktx_hole => e
| ktx_app1 K f => exp_app (K[/e]) f
| ktx_app2 f K => exp_app f (K[/e])
| ktx_let K f  => exp_let (K[/e]) f
| ktx_binop1 op K f => exp_binop op (K[/e]) f
| ktx_binop2 op f K => exp_binop op f (K[/e])
| ktx_proj K b => exp_proj (K[/e]) b
| ktx_if K e1 e2 => exp_if (K[/e]) e1 e2
| ktx_sample K => exp_sample (K[/e])
| ktx_score K => exp_score (K[/e])
end
where "K '[/' e ']' " := (ktx_plug K e)
.


Fixpoint ktx_comp (K J : ktx) {struct K} :=
match K with
| ktx_hole => J
| ktx_app1 K f => ktx_app1 (ktx_comp K J) f
| ktx_app2 f K => ktx_app2 f (ktx_comp K J)
| ktx_let K f  => ktx_let (ktx_comp K J) f
| ktx_binop1 op K f => ktx_binop1 op (ktx_comp K J) f
| ktx_binop2 op f K => ktx_binop2 op f (ktx_comp K J)
| ktx_proj K b => ktx_proj (ktx_comp K J) b
| ktx_if K e1 e2 => ktx_if (ktx_comp K J) e1 e2
| ktx_sample K => ktx_sample (ktx_comp K J)
| ktx_score K => ktx_score (ktx_comp K J)
end.

Lemma ktx_plug_comp
(K J : ktx) e :
K[/(J[/e])] = (ktx_comp K J)[/e].
Proof.
induction K ; simpl ; crush.
Qed.

Lemma ktx_plug_injection K e e': 
  K[/e] = K[/e'] → e = e'.
Proof.
  induction K in e, e' |-*; cbn;
  intros Heq; 
  inversion Heq; 
  auto.
Qed.

Lemma plug_exn_is_not_val K (v : val0): 
  K[/exp_exn] ≠ v.
Proof.
  destruct K; destruct v; intros [=].
Qed.

Lemma ktx_plug_is_exp_exn_inv K e : 
  K[/e] = exp_exn →
  K = ktx_hole ∧ e = exp_exn.
Proof.
  destruct K; cbn; intros [=].
  auto.
Qed.

Lemma ktx_plug_is_val_inv K : ∀ e v,
K[/e] = exp_val v →
K = ktx_hole ∧ e = v.
Proof.
induction K ; crush.
Qed.

Ltac ktx_plug_is_val_absurd :=
repeat match goal with
| [ H : ktx_plug ?K ?e = exp_val ?v |- _ ] =>
  exfalso ; apply ktx_plug_is_val_inv in H ;
  destruct H as [? ?]
| [ H : exp_val ?v = ktx_plug ?K ?e |- _ ] =>
  apply eq_sym in H
| [ H : exp_app _ _ = exp_val _ |- _ ] =>
  discriminate H
| [ H : exp_let _ _ = exp_val _ |- _ ] =>
  discriminate H
| [ H : exp_binop _ _ _ = exp_val _ |- _ ] =>
  discriminate H
| [ H : exp_proj _ _ = exp_val _ |- _ ] =>
  discriminate H
| [ H : exp_if _ _ _ = exp_val _ |- _ ] =>
  discriminate H
| [ H : exp_sample _ = exp_val _ |- _ ] =>
  discriminate H
| [ H : exp_score _ = exp_val _ |- _ ] =>
  discriminate H
| [ H : exp_exn = exp_val _ |- _ ] =>
  discriminate H
end.

Lemma exp_val_dec V (e : exp V) :
{ v & e = exp_val v } + { ∀ v, e = exp_val v → False }.
Proof.
destruct e ; (
  (left ; eexists ; reflexivity) ||
  (right ; intros v H ; inversion H)
).
Defined.

Ltac bind_ktx_app1 := repeat match goal with
| [ |- context[exp_app ?e1 ?e2] ] =>
  replace (exp_app e1 e2) with (ktx_plug (ktx_app1 ktx_hole e2) e1)
  by trivial
end.
Ltac bind_ktx_app2 := repeat match goal with
| [ |- context[exp_app (exp_val ?v) ?e] ] =>
  replace (exp_app (exp_val v) e) with (ktx_plug (ktx_app2 v ktx_hole) e)
  by trivial
end.
Ltac bind_ktx_let := repeat match goal with
| [ |- context[exp_let ?e1 ?e2] ] =>
  replace (exp_let e1 e2) with (ktx_plug (ktx_let ktx_hole e2) e1)
  by trivial
end.
Ltac bind_ktx_binop1 := repeat match goal with
| [ |- context[exp_binop ?op ?e1 ?e2] ] =>
  replace (exp_binop op e1 e2) with (ktx_plug (ktx_binop1 op ktx_hole e2) e1)
  by trivial
end.
Ltac bind_ktx_binop2 := repeat match goal with
| [ |- context[exp_binop ?op (exp_val ?v) ?e] ] =>
  replace (exp_binop op (exp_val v) e) with (ktx_plug (ktx_binop2 op v ktx_hole) e)
  by trivial
end.
Ltac bind_ktx_proj := repeat match goal with
| [ |- context[exp_proj ?e ?b] ] =>
  replace (exp_proj e b) with (ktx_plug (ktx_proj ktx_hole b) e)
  by trivial
end.
Ltac bind_ktx_if := repeat match goal with
| [ |- context[exp_if ?e1 ?e2 ?e3] ] =>
  replace (exp_if e1 e2 e3) with (ktx_plug (ktx_if ktx_hole e2 e3) e1)
  by trivial
end.
Ltac bind_ktx_sample := repeat match goal with
| [ |- context[exp_sample ?e] ] =>
  replace (exp_sample e) with (ktx_plug (ktx_sample ktx_hole) e)
  by trivial
end.
Ltac bind_ktx_score := repeat match goal with
| [ |- context[exp_score ?e] ] =>
  replace (exp_score e) with (ktx_plug (ktx_score ktx_hole) e)
  by trivial
end.

Fact exp_ktx_exn_dec_aux1 e1 e2 K
(H : exp_app e1 e2 =  K[/exp_exn])
(Notval_e1 : ∀ v, e1 = exp_val v → False) :
∃ K', e1 = K'[/exp_exn] ∧ K = ktx_app1 K' e2.
Proof.
destruct K; simpl in H.
+ inversion H.
+ inversion H; subst; clear H. eauto.
+ inversion H; subst; clear H. exfalso. eapply Notval_e1. reflexivity.
+ inversion H.
+ inversion H.
+ inversion H.
+ inversion H.
+ inversion H.
+ inversion H.
+ inversion H.
Qed.

Fact exp_ktx_exn_dec_aux2 (v : val0) e K
(H : exp_app v e = K[/exp_exn]) :
∃ K', e = K'[/exp_exn] ∧ K = ktx_app2 v K'.
Proof.
destruct K; simpl in H.
+ inversion H.
+ inversion H; subst; clear H. ktx_plug_is_val_absurd.
+ inversion H; subst; clear H. eexists; eauto.
+ inversion H.
+ inversion H.
+ inversion H.
+ inversion H.
+ inversion H.
+ inversion H.
+ inversion H.
Qed.

Fixpoint exp_ktx_exn_dec (e : exp0) {struct e}:
{ K & e = K[/exp_exn] } + { ∀ K, e = K[/exp_exn] → False }.
Proof.
destruct e.
+ right. intros. ktx_plug_is_val_absurd.
+ destruct (exp_ktx_exn_dec e1) as [ [K ?] | ]; subst.
  - left. eexists (ktx_app1 K _). reflexivity.
  - destruct (exp_val_dec e1) as [ [v ?] | ]; subst.
    2:{
      right. intros K H.
      destruct K; simpl in H; inversion H; subst; clear H; eauto.
    }
    destruct (exp_ktx_exn_dec e2) as [ [K ?] | ]; subst.
    * left. eexists (ktx_app2 _ K). reflexivity.
    * right. intros K H.
      destruct K; simpl in H; inversion H; subst; clear H; eauto.
+ destruct (exp_ktx_exn_dec e1) as [ [K ?] | ]; subst.
  - left. eexists (ktx_let K _). reflexivity.
  - right. intros K H.
    destruct K; simpl in H; inversion H; subst; clear H; eauto.
+ destruct (exp_ktx_exn_dec e1) as [ [K ?] | ]; subst.
  - left. eexists (ktx_binop1 _ K _). reflexivity.
  - destruct (exp_val_dec e1) as [ [v ?] | ]; subst.
    2:{
      right. intros K H.
      destruct K; simpl in H; inversion H; subst ; clear H; eauto.
    }
    destruct (exp_ktx_exn_dec e2) as [ [K ?] | ]; subst.
    * left. eexists (ktx_binop2 _ _ K). reflexivity.
    * right. intros K H. 
      destruct K; simpl in H; inversion H; subst ; clear H; eauto.
+ destruct (exp_ktx_exn_dec e) as [ [K ?] | ]; subst.
  - left. eexists (ktx_proj K _). reflexivity.
  - right. intros K H.
    destruct K; simpl in H; inversion H; subst; clear H; eauto.
+ destruct (exp_ktx_exn_dec e1) as [ [K ?] | ]; subst.
  - left. eexists (ktx_if K _ _). reflexivity.
  - right. intros K H.
    destruct K; simpl in H; inversion H; subst; clear H; eauto.
+ destruct (exp_ktx_exn_dec e) as [ [K ?] | ]; subst.
  - left. eexists (ktx_sample K). reflexivity.
  - right. intros K H.
    destruct K; simpl in H; inversion H; subst; clear H; eauto.
+ destruct (exp_ktx_exn_dec e) as [ [K ?] | ]; subst.
  - left. eexists (ktx_score K). reflexivity.
  - right. intros K H.
    destruct K; simpl in H; inversion H; subst; clear H; eauto.
+ left. exists ktx_hole. reflexivity.
Defined.
