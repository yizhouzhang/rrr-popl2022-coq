Require Import RRR.Lebesgue.Lebesgue.
Require Import RRR.Lang.Lang.
Require Import RRR.Rel.Relations.
Require Import RRR.Rel.Compatibility.
Require Import Omega.

Fixpoint exp_fundamental
(V : Set) (Γ : V → ty) e T
(W : wf_exp Γ e T) {struct W} :
ERel_open Γ T e e
with val_fundamental
(V : Set) (Γ : V → ty) v T
(W : wf_val Γ v T) {struct W} :
VRel_open Γ T v v.
Proof.
{
  destruct W.
  + apply compat_exp_val. 2:{ assumption. } 1:{ assumption. }
    apply val_fundamental. assumption.
  + eapply compat_exp_app.
    2:{ apply exp_fundamental. eassumption. }
    1:{ apply exp_fundamental. assumption. }
  + eapply compat_exp_let.
    2:{ apply exp_fundamental. eassumption. }
    1:{ apply exp_fundamental. assumption. }
  + apply compat_exp_binop.
    2:{ apply exp_fundamental. eassumption. }
    1:{ apply exp_fundamental. assumption. }
  + apply compat_exp_proj. apply exp_fundamental. assumption.
  + apply compat_exp_if; apply exp_fundamental; assumption.
  + apply compat_exp_sample. apply exp_fundamental. assumption.
  + apply compat_exp_score. apply exp_fundamental. assumption.
  + apply compat_exp_diverge.
}
{
  destruct W.
  + apply compat_val_var.
  + apply compat_val_real. 
  + apply compat_val_unit.
  + apply compat_val_bool.
  + apply compat_val_fun; try assumption. apply exp_fundamental. assumption.
  + apply compat_val_fix; try assumption. apply exp_fundamental. assumption.
  + apply compat_val_pair; apply val_fundamental; assumption.
  + apply compat_val_unif.
  + apply compat_val_query; try assumption.
    apply exp_fundamental. assumption.
}
Qed.

Theorem fundamental
(V : Set) (Γ : V → ty) e T
(W : wf_exp Γ e T) :
ERel_open Γ T e e.
Proof.
apply exp_fundamental; assumption.
Qed.

Lemma Ciu_in_ERel (V : Set) Γ T (e₁ e₂ : exp V) :
Ciu_open Γ T e₁ e₂ →
ERel_open Γ T e₁ e₂.
Proof.
intro HC. specialize HC as Wf_e. destruct Wf_e as [Wf_e₁ Wf_e₂].
apply ERel_Ciu_ERel_open with (e₂' := e₁).
2:{ apply HC. }
apply fundamental. apply Wf_e₁.
Qed.
