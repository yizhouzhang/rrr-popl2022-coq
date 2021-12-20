Require Import RRR.Lebesgue.Lebesgue.
Require Import RRR.Lang.Lang.
Require Import RRR.Rel.Relations.
Require Import RRR.Rel.Compatibility.
Require Import RRR.Rel.Fundamental.
Require Import RRR.Rel.Adequacy.
Require Import Omega.

Section section_congruence.

Hint Constructors wf_exp wf_val wf_ctx : core.

Fixpoint congruence V (e₁ e₂ : exp V)
(Γ : V → ty) (T T₀ : ty) (C : ctx V)
(W : wf_ctx C Γ T T₀) {struct W} :
ERel_open Γ T e₁ e₂ →
ERel_open ∅→ T₀ (ctx_plug C e₁) (ctx_plug C e₂).
Proof.
intro He.
specialize He as Wf_e. destruct Wf_e as [[Wf_e₁ Wf_e₂] _].
destruct W ; simpl.
+ apply He.
+ eapply congruence; eauto.
  apply compat_exp_val.
  2:{ constructor; assumption.  }
  1:{ constructor; assumption.  }
  apply compat_val_fun; auto.
+ eapply congruence; eauto.
  apply compat_exp_val.
  2:{ constructor; assumption.  }
  1:{ constructor; assumption.  }
  apply compat_val_fix; auto.
+ eapply congruence; eauto.
  apply compat_exp_val.
  2:{ constructor; assumption.  }
  1:{ constructor; assumption.  }
  apply compat_val_query; assumption.
+ eapply congruence; eauto.
  eapply compat_exp_app.
  2:{ apply exp_fundamental. eassumption. }
  apply He.
+ eapply congruence; eauto.
  eapply compat_exp_app.
  1:{ apply exp_fundamental. eassumption. }
  apply He.
+ eapply congruence; eauto.
  eapply compat_exp_let.
  2:{ apply exp_fundamental. eassumption. }
  apply He.
+ eapply congruence; eauto.
  eapply compat_exp_let.
  1:{ apply exp_fundamental. eassumption. }
  apply He.
+ eapply congruence; eauto.
  eapply compat_exp_binop.
  2:{ apply exp_fundamental. eassumption. }
  apply He.
+ eapply congruence; eauto.
  eapply compat_exp_binop.
  1:{ apply exp_fundamental. eassumption. }
  apply He.
+ eapply congruence; eauto.
  apply compat_exp_proj. apply He.
+ eapply congruence; eauto.
  apply compat_exp_if. apply He.
  eapply exp_fundamental; assumption.
  eapply exp_fundamental; assumption.
  + eapply congruence; eauto.
    apply compat_exp_if.
    eapply exp_fundamental; assumption.
    assumption.
    eapply exp_fundamental; assumption.
  + eapply congruence; eauto.
    apply compat_exp_if.
    eapply exp_fundamental; assumption.
    eapply exp_fundamental; assumption.
    assumption.
+ eapply congruence; eauto.
  apply compat_exp_sample. apply He.
+ eapply congruence; eauto.
  apply compat_exp_score. apply He.
Qed.

End section_congruence.

Theorem soundness (V : Set) (Γ : V → ty) T e₁ e₂ :
ERel_open Γ T e₁ e₂ →
ctx_approx Γ T e₁ e₂.
Proof.
intro He.
intros C W.
apply adequacy.
eapply congruence; eassumption.
Qed.

Definition Ciu_equiv (V : Set) (Γ : V → 𝕋) (τ : 𝕋) (e₁ e₂ : exp V) :=
(wf_exp Γ e₁ τ ∧ wf_exp Γ e₂ τ) ∧
∀ γ K, wf_env γ Γ →
μNS_inf (ktx_plug K (V_bind_exp γ e₁)) = μNS_inf (ktx_plug K (V_bind_exp γ e₂)) ∧
μTV_sup (ktx_plug K (V_bind_exp γ e₁)) = μTV_sup (ktx_plug K (V_bind_exp γ e₂)).

Lemma Ciu_open_antisym :
∀ (V : Set) (Γ : V → 𝕋) (τ : 𝕋) (e₁ e₂ : exp V),
Ciu_equiv V Γ τ e₁ e₂ →
Ciu_open Γ τ e₁ e₂ ∧ Ciu_open Γ τ e₂ e₁.
Proof.
  intros V Γ τ e₁ e₂ H.
  destruct H.
  split.
  + split.
    - tauto.
    - intros n γ wf_env.
      split; specialize H0 with (γ := γ) (K := K);
      apply H0 in wf_env; destruct wf_env.
      * eapply ennr_le_trans.
        2:{
          apply μNS_inf_le_μNS.
        }
        rewrite H1.
        auto.
      * intro Ev.
        eapply ennr_le_trans.
        1:{
          apply μTV_sup_ge_μTV.
        }
        rewrite H2.
        auto.
  + split.
    - tauto.
    - intros n γ wf_env.
      split; specialize H0 with (γ := γ) (K := K);
      apply H0 in wf_env; destruct wf_env.
      * eapply ennr_le_trans.
        2:{
          apply μNS_inf_le_μNS.
        }
        rewrite H1.
        auto.
      * intro Ev.
        eapply ennr_le_trans.
        1:{
          apply μTV_sup_ge_μTV.
        }
        rewrite H2.
        auto.
Qed.

Lemma Ciu_equiv_ctx_equiv :
∀ V Γ τ e₁ e₂,
@Ciu_equiv V Γ τ e₁ e₂ → ctx_equiv Γ τ e₁ e₂.
Proof.
  intros V Γ τ e₁ e₂ H.
  apply ctx_approx_antisym.
  split;
  apply soundness;
  apply Ciu_in_ERel;
  apply Ciu_open_antisym in H;
  tauto.
Qed.