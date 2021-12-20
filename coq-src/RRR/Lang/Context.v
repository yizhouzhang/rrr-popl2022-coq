Require Export RRR.Lebesgue.Lebesgue.
Require Export RRR.Lang.Syntax.
Require Export RRR.Lang.Bindings.
Require Export RRR.Lang.BindingsFacts.
Require Export RRR.Lang.Evaluation.
Require Export RRR.Lang.Measure.
Require Export RRR.Lang.Static.

Set Implicit Arguments.
Implicit Types V : Set.

Inductive ctx : Set → Type :=
| ctx_top : ctx ∅
| ctx_fun : ∀ V, ctx V → ctx (inc V)
| ctx_fix : ∀ V, ctx V → ctx (inc V)
| ctx_query : ∀ V, ctx V → ctx V
| ctx_app1 : ∀ V, ctx V → exp V → ctx V
| ctx_app2 : ∀ V, ctx V → exp V → ctx V
| ctx_let1 : ∀ V, ctx V → exp (inc V) → ctx V
| ctx_let2 : ∀ V, ctx V → exp V → ctx (inc V)
| ctx_binop1 : ∀ V, ctx V → binop → exp V → ctx V
| ctx_binop2 : ∀ V, ctx V → binop → exp V → ctx V
| ctx_proj : ∀ V, ctx V → bool → ctx V
| ctx_if1 :  ∀ V, ctx V → exp V → exp V → ctx V
| ctx_if2 :  ∀ V, ctx V → exp V → exp V → ctx V
| ctx_if3 :  ∀ V, ctx V → exp V → exp V → ctx V
| ctx_sample : ∀ V, ctx V → ctx V
| ctx_score : ∀ V, ctx V → ctx V
.

Fixpoint ctx_plug V (C : ctx V) (e : exp V) : exp0.
Proof.
destruct C as [
  | ? C | ? C | ? C | ? C f | ? C f | ? C f | ? C f | ? C b f | ? C b f | ? C b | ? C E1 E2 | ? C E1 E2 | ? C E1 E2 | ? C | ? C
].
+ apply e.
+ apply (ctx_plug _ C (val_fun e)).
+ apply (ctx_plug _ C (val_fix e)).
+ apply (ctx_plug _ C (val_query e)).
+ apply (ctx_plug _ C (exp_app e f)).
+ apply (ctx_plug _ C (exp_app f e)).
+ apply (ctx_plug _ C (exp_let e f)).
+ apply (ctx_plug _ C (exp_let f e)).
+ apply (ctx_plug _ C (exp_binop b e f)).
+ apply (ctx_plug _ C (exp_binop b f e)).
+ apply (ctx_plug _ C (exp_proj e b)).
+ apply (ctx_plug _ C (exp_if e E1 E2)).
+ apply (ctx_plug _ C (exp_if E1 e E2)).
+ apply (ctx_plug _ C (exp_if E1 E2 e)).
+ apply (ctx_plug _ C (exp_sample e)).
+ apply (ctx_plug _ C (exp_score e)).
Defined.

Inductive wf_ctx : ∀ V, ctx V → (V → ty) → ty → ty → Type :=
| wf_ctx_top :
  ∀ T₀, wf_ctx ctx_top ∅→ T₀ T₀
| wf_ctx_fun :
  ∀ T₀ V C (Γ : V → ty) T U,
  wf_ctx C Γ (ty_fun T U) T₀ →
  wf_ctx (ctx_fun C) (env_ext Γ T) U T₀
| wf_ctx_fix :
  ∀ T₀ V C (Γ : V → ty) T,
  wf_ctx C Γ (ty_fun ty_unit T) T₀ →
  wf_ctx (ctx_fix C) (env_ext Γ (ty_fun ty_unit T)) T T₀
| wf_ctx_query :
  ∀ T₀ V C (Γ : V → ty) T,
  wf_ctx C Γ (ty_dist T) T₀ →
  T = ℝ ∨ T = ty_bool →
  wf_ctx (ctx_query C) Γ T T₀
| wf_ctx_app1 :
  ∀ T₀ V C (Γ : V → ty) T U f,
  wf_ctx C Γ U T₀ →
  wf_exp Γ f T →
  wf_ctx (ctx_app1 C f) Γ (ty_fun T U) T₀
| wf_ctx_app2 :
  ∀ T₀ V C (Γ : V → ty) T U f,
  wf_ctx C Γ U T₀ →
  wf_exp Γ f (ty_fun T U) →
  wf_ctx (ctx_app2 C f) Γ T T₀
| wf_ctx_let1 :
  ∀ T₀ V C (Γ : V → ty) T U f,
  wf_ctx C Γ U T₀ →
  wf_exp (env_ext Γ T) f U →
  wf_ctx (ctx_let1 C f) Γ T T₀
| wf_ctx_let2 :
  ∀ T₀ V C (Γ : V → ty) T U f,
  wf_ctx C Γ U T₀ →
  wf_exp Γ f T →
  wf_ctx (ctx_let2 C f) (env_ext Γ T) U T₀
| wf_ctx_binop1 :
  ∀ T₀ V C (Γ : V → ty) op f,
  wf_ctx C Γ (binop_ty op) T₀ →
  wf_exp Γ f ℝ →
  wf_ctx (ctx_binop1 C op f) Γ ℝ T₀
| wf_ctx_binop2 :
  ∀ T₀ V C (Γ : V → ty) op f,
  wf_ctx C Γ (binop_ty op) T₀ →
  wf_exp Γ f ℝ →
  wf_ctx (ctx_binop2 C op f) Γ ℝ T₀
| wf_ctx_proj :
  ∀ T₀ V C (Γ : V → ty) TL TR (b : bool),
  wf_ctx C Γ (if b then TL else TR) T₀ →
  wf_ctx (ctx_proj C b) Γ (ty_pair TL TR) T₀
| wf_ctx_if1 :
  ∀ T₀ V C (Γ : V → ty) T f g,
  wf_ctx C Γ T T₀ →
  wf_exp Γ f T →
  wf_exp Γ g T →
  wf_ctx (ctx_if1 C f g) Γ ty_bool T₀
| wf_ctx_if2 :
    ∀ T₀ V C (Γ : V → ty) T f g,
      wf_ctx C Γ T T₀ →
      wf_exp Γ f ty_bool →
      wf_exp Γ g T →
      wf_ctx (ctx_if2 C f g) Γ T T₀
| wf_ctx_if3 :
     ∀ T₀ V C (Γ : V → ty) T f g,
      wf_ctx C Γ T T₀ →
      wf_exp Γ f ty_bool →
      wf_exp Γ g T →
      wf_ctx (ctx_if3 C f g) Γ T T₀
| wf_ctx_sample :
  ∀ T₀ V C (Γ : V → ty) T,
  wf_ctx C Γ T T₀ →
  wf_ctx (ctx_sample C) Γ (ty_dist T) T₀
| wf_ctx_score :
  ∀ T₀ V C (Γ : V → ty),
  wf_ctx C Γ ty_unit T₀ →
  wf_ctx (ctx_score C) Γ ℝ T₀
.

Section section_wf_ctx_plug.
Hint Constructors wf_exp wf_val : core.

Lemma wf_ctx_plug V (C : ctx V) Γ T R:
wf_ctx C Γ T R →
∀ e, wf_exp Γ e T → wf_exp ∅→ (ctx_plug C e) R.
Proof.
induction 1; simpl; intros e Wf_e; eauto.
Qed.

End section_wf_ctx_plug.

Open Scope ennr_scope.

Definition ctx_approx V (Γ : V → ty) T e₁ e₂ : Prop :=
∀ C, wf_ctx C Γ T ℝ →
∀ N,
μNS_inf (ctx_plug C e₂) ≤ μNS N (ctx_plug C e₁) ∧
∀ A, μTV N (ctx_plug C e₁) A ≤ μTV_sup (ctx_plug C e₂) A.

Definition ctx_equiv V (Γ : V → ty) T e₁ e₂ : Prop :=
∀ C, wf_ctx C Γ T ℝ →
μNS_inf (ctx_plug C e₁) = μNS_inf (ctx_plug C e₂) ∧
∀ A, μTV_sup (ctx_plug C e₁) A = μTV_sup (ctx_plug C e₂) A.

Lemma ctx_approx_antisym :
∀ V (Γ : V → ty) T e₁ e₂,
  ctx_equiv (Γ : V → ty) T e₁ e₂
↔ ctx_approx (Γ : V → ty) T e₁ e₂ ∧  ctx_approx (Γ : V → ty) T e₂ e₁.
Proof.
  split; intro.
  + split.
  - unfold ctx_equiv in *. unfold ctx_approx in *.
    intros. specialize H with C. apply H in X. destruct X.
    split.
    * eapply ennr_le_trans with (μNS N (ctx_plug C e₁)).
      eapply ennr_le_trans with (μNS_inf (ctx_plug C e₂)).
      auto. rewrite <- H0. eapply μNS_inf_le_μNS. auto.
    * intro. specialize H1 with A. rewrite <- H1. eapply μTV_sup_ge_μTV.
  - unfold ctx_equiv in *. unfold ctx_approx in *.
    intros. specialize H with C. apply H in X. destruct X.
    split.
    * eapply ennr_le_trans with (μNS N (ctx_plug C e₂)).
      rewrite H0. eapply μNS_inf_le_μNS. auto.
    * intro. specialize H1 with A. rewrite H1. eapply μTV_sup_ge_μTV.
  + destruct H. unfold ctx_approx in *. unfold ctx_equiv in *. intros.
    split.
  - assert (∀ N : nat,
            μNS_inf (ctx_plug C e₂) ≤ μNS N (ctx_plug C e₁)). eapply H. exact X.
    assert (∀ N : nat,
               μNS_inf (ctx_plug C e₁) ≤ μNS N (ctx_plug C e₂)). eapply H0. exact X.
    eapply μNS_inf_is_glb in H1. eapply μNS_inf_is_glb in H2.
    eapply ennr_le_antisym; auto.
  - assert (∀ N : nat, (∀ A : Event val0, μTV N (ctx_plug C e₁) A ≤ μTV_sup (ctx_plug C e₂) A)).
    eapply H. exact X.
    assert (∀ N : nat, (∀ A : Event val0, μTV N (ctx_plug C e₂) A ≤ μTV_sup (ctx_plug C e₁) A)).
    eapply H0. exact X.
    intros A.
    assert ( ∀ (N : nat),
               μTV N (ctx_plug C e₁) A ≤ μTV_sup (ctx_plug C e₂) A).
    intro. apply H1.
    assert ( ∀ (N : nat),
               μTV N (ctx_plug C e₂) A ≤ μTV_sup (ctx_plug C e₁) A).
    intro. apply H2.
    eapply μTV_sup_is_lub in H3.
    eapply μTV_sup_is_lub in H4.
    eapply ennr_le_antisym; auto.
Qed.
