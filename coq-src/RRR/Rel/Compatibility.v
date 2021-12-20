Require Import RRR.Lebesgue.Lebesgue.
Require Import RRR.Lang.Lang.
Require Import RRR.Rel.Relations.
Require Import RRR.Rel.UtilMeasures.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Minus.
Require Import Coq.micromega.Lra.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Section section_compat.
Context (V : Set).
Context (Γ : V → ty).

Lemma compat_exp_proj TL TR e₁ e₂ (b : bool) :
ERel_open Γ (ty_pair TL TR) e₁ e₂ →
ERel_open Γ (if b then TL else TR) (exp_proj e₁ b) (exp_proj e₂ b).
Proof.
intros [[Wf_e₁ Wf_e₂] He]. split; [split|].
2:{ constructor; assumption. }
1:{ constructor; assumption. }
clear Wf_e₁ Wf_e₂.
intros N γ₁ γ₂ Hγ.
simpl V_bind_exp.
bind_ktx_proj.
eapply ERel_ktx_plug with (N := N).
3:{ apply He. apply Hγ. }
2:{ omega. }
clear.
intros N' HN' v₁ v₂ Hv.
destruct Hv as [u₁ [u₂ [w₁ [w₂ [Hv₁ [Hv₂ [Hu Hw]]]]]]].
subst.
simpl.
eapply ERel_monotone with (N := S N').
2:{ omega. }
destruct b.
+ eapply ERel_sss_l.
  { intros. constructor. }
  eapply ERel_sss_r.
  { intros. constructor. }
  apply VRel_in_ERel.
  apply Hu.
+ eapply ERel_sss_l.
  1:{ intros ; constructor. }
  eapply ERel_sss_r.
  1:{ intros ; constructor. }
  apply VRel_in_ERel.
  apply Hw.
Qed.

Lemma compat_exp_if T p₁ t₁ e₁ p₂ t₂ e₂ :
  ERel_open Γ ty_bool p₁ p₂ →
  ERel_open Γ T t₁ t₂ →
  ERel_open Γ T e₁ e₂ →
  ERel_open Γ T (exp_if p₁ t₁ e₁) (exp_if p₂ t₂ e₂).
Proof.
  intros [[Wf_p₁ Wf_p₂] Hp] [[Wf_t₁ Wf_t₂] Ht] [[Wf_e₁ Wf_e₂] He].
  split; [split|].
  - constructor; eassumption.
  - constructor; eassumption.
  - intros.
    simpl V_bind_exp.
    bind_ktx_if.
    eapply ERel_ktx_plug with (N := N).
    3:{ apply Hp. exact H. }
    2:{ auto. }
    intros N' HN' v₁ v₂ Hv.
    (* destruct Hv. *)
    simpl.
    eapply ERel_monotone with (N := S N').
    2:{ omega. }
    inversion Hv. destruct x. destruct H0.
    + eapply ERel_sss_l.
      { intros. rewrite H0. eapply sss_then. }
      eapply ERel_sss_r.
      { intros. rewrite H1. eapply sss_then. }
      eapply Ht. eapply EnvRel_monotone. { exact H. } { exact HN'. }
    + eapply ERel_sss_l. destruct H0.
      { intros. rewrite e. eapply sss_else. }
      eapply ERel_sss_r.
      { intros. destruct H0. rewrite e0. eapply sss_else. }
      eapply He. eapply EnvRel_monotone. { exact H. } { exact HN'. }
Qed.

Lemma compat_exp_app T U f₁ e₁ f₂ e₂ :
ERel_open Γ (ty_fun T U) f₁ f₂ →
ERel_open Γ T e₁ e₂ →
ERel_open Γ U (exp_app f₁ e₁) (exp_app f₂ e₂).
Proof.
intros [[Wf_f₁ Wf_f₂] Hf] [[Wf_e₁ Wf_e₂] He].
split; [split|].
2:{ econstructor; eassumption. }
1:{ econstructor; eassumption. }
clear Wf_f₁ Wf_f₂ Wf_e₁ Wf_e₂.
intros N γ₁ γ₂ Hγ.
simpl V_bind_exp.
repeat match goal with
| [ |- context[exp_app ?e ?e'] ] =>
  replace (exp_app e e') with
    (ktx_plug (ktx_app1 ktx_hole e') e) by trivial
end.
eapply ERel_ktx_plug with (N := N).
3:{ apply Hf. apply Hγ. }
2:{ omega. }
intros N' HN' v₁ v₂ Hv.
simpl ktx_plug.
repeat match goal with
| [ |- context[exp_app (exp_val ?v) ?e'] ] =>
  replace (exp_app (exp_val v) e') with
    (ktx_plug (ktx_app2 v ktx_hole) e') by trivial
end.
eapply ERel_ktx_plug with (N := N').
3:{
  apply He.
  eapply EnvRel_monotone ; [ apply Hγ | omega ].
}
2:{ omega. }
clear- Hv. rename N' into N.
intros N' HN' u₁ u₂ Hu.
simpl ktx_plug.
simpl in Hv.
apply Hv; [ omega | ].
apply Hu.
Qed.

Lemma compat_exp_let T U f₁ e₁ f₂ e₂ :
ERel_open Γ T f₁ f₂ →
ERel_open (env_ext Γ T) U e₁ e₂ →
ERel_open Γ U (exp_let f₁ e₁) (exp_let f₂ e₂).
Proof.
intros [[Wf_f₁ Wf_f₂] Hf] [[Wf_e₁ Wf_e₂] He].
split; [split|].
2:{ econstructor; eassumption. }
1:{ econstructor; eassumption. }
clear Wf_f₁ Wf_f₂ Wf_e₁ Wf_e₂.
intros N γ₁ γ₂ Hγ.
simpl V_bind_exp.
repeat match goal with
| [ |- context[exp_let ?e ?e'] ] =>
  replace (exp_let e e') with
    (ktx_plug (ktx_let ktx_hole e') e) by trivial
end.
eapply ERel_ktx_plug with (N := N).
3:{ apply Hf. apply Hγ. }
2:{ omega. }
intros N' HN' v₁ v₂ Hv.
simpl ktx_plug.
eapply ERel_monotone with (N := S N').
2:{ omega. }
eapply ERel_sss_l.
{ intros. constructor. }
eapply ERel_sss_r.
{ intros. constructor. }
repeat erewrite V_bind_bind_exp with (g := env_ext _ _).
1:{
  apply He.
  intro x. destruct x as [|x]; simpl.
  2:{ eapply VRel_monotone; try apply Hγ. omega. }
  eapply VRel_monotone; try apply Hv. omega.
}
+ clear. intro x; destruct x as [|x]; simpl; [reflexivity|].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id; reflexivity.
+ clear. intro x; destruct x as [|x]; simpl; [reflexivity|].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id; reflexivity.
Qed.

Lemma compat_exp_binop op f₁ e₁ f₂ e₂ :
ERel_open Γ ℝ f₁ f₂ →
ERel_open Γ ℝ e₁ e₂ →
ERel_open Γ (binop_ty op) (exp_binop op f₁ e₁) (exp_binop op f₂ e₂).
Proof.
intros [[Wf_f₁ Wf_f₂] Hf] [[Wf_e₁ Wf_e₂] He].
split; [split|].
2:{ econstructor; eassumption. }
1:{ econstructor; eassumption. }
clear Wf_f₁ Wf_f₂ Wf_e₁ Wf_e₂.
intros N γ₁ γ₂ Hγ.
simpl V_bind_exp.
bind_ktx_binop1.
eapply ERel_ktx_plug with (N := N).
3:{ apply Hf. apply Hγ. }
2:{ omega. }
intros N' HN' v₁ v₂ Hv.
simpl ktx_plug.
bind_ktx_binop2.
eapply ERel_ktx_plug with (N := N').
3:{
  apply He.
  eapply EnvRel_monotone ; [ apply Hγ | omega ].
}
2:{ omega. }
clear - Hv. rename N' into M.
intros N HN u₁ u₂ Hu.
simpl ktx_plug.
simpl in Hv, Hu.
destruct Hv as [rv [? ?]]. destruct Hu as [ru [? ?]]. subst.
eapply ERel_monotone with (N := S N).
2:{ omega. }
destruct (binop_interp op (val_real rv) (val_real ru)) eqn:Hop.
2:{
  assert (stop 0 (exp_binop op (val_real rv) (val_real ru))) as Stop.
  1:{ 
    split.
    + do 4 intro. intro Step. 
      inversion Step; subst; try rewrite Hop in *; try match goal with
      | [ H : sss _ _ (exp_val _) _ _ _ |- _ ] => inversion H
      | [ H : None = Some _ |- _ ] => inversion H
      end.
    + intros K Q.
      destruct K; simpl in Q; inversion Q; subst.
      - ktx_plug_is_val_absurd.
      - ktx_plug_is_val_absurd.
  }
  eapply ERel_stuck with (N₁ := O) (N₂ := O).
  4:{ intros. ktx_plug_is_val_absurd. }
  3:{ apply Stop. }
  2:{ intros. ktx_plug_is_val_absurd. }
  1:{ apply Stop. }
}
eapply ERel_sss_l.
{ intros. constructor. apply Hop. }
eapply ERel_sss_r.
{ intros. constructor. apply Hop. }
destruct op; simpl in Hop; inversion Hop; subst; clear Hop.
+ apply VRel_in_ERel. simpl. eexists; split; reflexivity.
+ apply VRel_in_ERel. simpl. eexists; split; reflexivity.
+ apply VRel_in_ERel. simpl. eexists; split; reflexivity.
+ apply VRel_in_ERel. simpl. eexists; split; reflexivity.
+ apply VRel_in_ERel. simpl. eexists; split; reflexivity.
Qed.

Lemma compat_exp_score e₁ e₂ :
ERel_open Γ ℝ e₁ e₂ →
ERel_open Γ ty_unit (exp_score e₁) (exp_score e₂).
Proof.
intros [[Wf_e₁ Wf_e₂] He].
split; [split|].
2:{ constructor; assumption. }
1:{ constructor; assumption. }
clear Wf_e₁ Wf_e₂.
intros N γ₁ γ₂ Hγ.
simpl V_bind_exp.
bind_ktx_score.
eapply ERel_ktx_plug with (N := N).
3:{ apply He. apply Hγ. }
2:{ omega. }
clear.
intros N' HN'. clear. rename N' into N.
intros v₁ v₂ Hv.
destruct Hv as [r [Hv₁ Hv₂]].
subst.
simpl ktx_plug.
eapply ERel_monotone with (N := S N).
2:{ omega. }
(* If r ≤ 0 or r > 1, score r is stuck. *)
assert (
  ¬ (0 < r)%R ∨ ¬ (r ≤ 1)%R →
  ERel ty_unit (S N) (exp_score (val_real r)) (exp_score (val_real r))
).
1:{
  intro H.
  assert (Stop : stop 0 (exp_score (val_real r))).
  1:{ 
    split.
    + do 4 intro. intro Step.
      inversion Step; subst. 2:{
        match goal with
        | [ Hsss : sss _ _ (exp_val _) _ _ _ |- _ ] => inversion Hsss
        end.
      }
      destruct H as [H | H]; subst; repeat match goal with
      | [ H1 : ?P, H2 : ¬ ?P |- _ ] => apply (H2 H1)
      | [ Hsss : sss _ _ (exp_val _) _ _ _ |- _ ] => inversion Hsss
      end.
    + intros K Q. destruct K; simpl in Q; inversion Q; subst.
      ktx_plug_is_val_absurd.
  }
  eapply ERel_stuck with (N₁ := O) (N₂ := O).
  4:{ intros. ktx_plug_is_val_absurd. }
  3:{ apply Stop. }
  2:{ intros. ktx_plug_is_val_absurd. }
  1:{ apply Stop. }
}
destruct (Rlt_dec 0 r) as [Hr0|Hr0], (Rle_dec r 1) as [Hr1|Hr1].
4:{ apply H. auto. } 
3:{ apply H. auto. } 
2:{ apply H. auto. } 

intros N' HN'. clear- Hr0 Hr1. rename N' into N. intros K₁ K₂ HK.
destruct N as [|N].
1:{ apply ORel_O_nonval. intros. ktx_plug_is_val_absurd. }
assert (VRel ty_unit N val_unit val_unit) as Hv.
1:{ simpl. auto. }
apply HK in Hv ; [|omega].
assert (∀ K N t, sss (eval N) t (ktx_plug K (exp_score (val_real r))) t
  (ktx_plug K val_unit) (finite r (Rlt_le _ _ Hr0))) as Step.
1:{ intros. apply ktx_congruence. unshelve apply sss_score; assumption. }

unfold ORel.
erewrite sss_preserves_μNS_inf by apply Step.
destruct Hv as [NS TV]. split.
+ erewrite sss_preserves_μNS by apply Step.
  apply ennr_mult_le_compat_r. apply NS.
+ intro A. erewrite sss_preserves_μTV by apply Step.
  erewrite sss_preserves_μTV_sup by apply Step.
  simpl. apply ennr_mult_le_compat_r. apply TV.
Qed.

Lemma compat_exp_sample T e₁ e₂ :
ERel_open Γ (ty_dist T) e₁ e₂ →
ERel_open Γ T (exp_sample e₁) (exp_sample e₂).
Proof.
intros [[Wf_e₁ Wf_e₂] He].
split; [split|].
2:{ constructor; assumption. }
1:{ constructor; assumption. }
clear Wf_e₁ Wf_e₂.
intros N γ₁ γ₂ Hγ.
simpl V_bind_exp.
bind_ktx_sample.
eapply ERel_ktx_plug with (N := N).
3:{ apply He. apply Hγ. }
2:{ omega. }
clear.
intros N' HN' v₁ v₂ Hv.
simpl ktx_plug.
simpl in Hv.
apply Hv.
Qed.

Lemma compat_exp_val T v₁ v₂ :
wf_val Γ v₁ T → wf_val Γ v₂ T →
VRel_open Γ T v₁ v₂ →
ERel_open Γ T v₁ v₂.
Proof.
intros Wf_v₁ Wf_v₂ Hv.
split; [split|].
2:{ constructor; assumption. }
1:{ constructor; assumption. }
intros N γ₁ γ₂ Hγ.
simpl.
apply VRel_in_ERel.
apply Hv. apply Hγ.
Qed.

Lemma compat_exp_diverge T :
ERel_open Γ T exp_exn exp_exn.
Proof.
split; [split|].
2:{ constructor. }
1:{ constructor. }
intros N γ₁ γ₂ Hγ. simpl. clear.
induction N.
1:{ apply ERel_O_nonval. intros. ktx_plug_is_val_absurd. }
apply ERel_exn.
Qed.

Lemma compat_val_var x :
VRel_open Γ (Γ x) (val_var x) (val_var x).
Proof.
intros N γ₁ γ₂ Hγ.
simpl.
apply Hγ.
Qed.

Lemma compat_val_real r :
VRel_open Γ ℝ (val_real r) (val_real r).
Proof.
intros N γ₁ γ₂ Hγ.
simpl.
eexists ; split ; reflexivity.
Qed.

Lemma compat_val_unit :
VRel_open Γ 𝟙 val_unit val_unit.
Proof.
intros N γ₁ γ₂ Hγ.
simpl.
split ; reflexivity.
Qed.

Lemma compat_val_bool b :
VRel_open Γ 𝟚 (val_bool b) (val_bool b).
Proof.
intros N γ₁ γ₂ Hγ.
simpl.
eexists ; split ; reflexivity.
Qed.

Lemma compat_val_pair TL TR v₁ v₂ u₁ u₂ :
VRel_open Γ TL v₁ v₂ →
VRel_open Γ TR u₁ u₂ →
VRel_open Γ (ty_pair TL TR) (val_pair v₁ u₁) (val_pair v₂ u₂).
Proof.
intros Hv Hu.
intros N γ₁ γ₂ Hγ.
simpl V_bind_val.
simpl VRel.
do 4 eexists. repeat split.
+ eapply VRel_monotone.
  1:{ apply Hv. apply Hγ. }
  omega.
+ eapply VRel_monotone.
  1:{ apply Hu. apply Hγ. }
  omega.
Qed.

Lemma compat_val_fun T U e₁ e₂ :
ERel_open (env_ext Γ U) T e₁ e₂ →
VRel_open Γ (ty_fun U T) (val_fun e₁) (val_fun e₂).
Proof.
intros [[Wf_e₁ Wf_e₂] He] N γ₁ γ₂ Hγ.
simpl V_bind_val.
simpl VRel.
split; [|split].
1:{
  constructor. eapply V_bind_wf_exp. 1:{ apply Wf_e₁. }
  intro x; destruct x as [|x]; simpl. 1:{ constructor. }
  specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?].
  eapply V_map_wf_val. 1:{ eassumption. } auto.
}
1:{
  constructor. eapply V_bind_wf_exp. 1:{ apply Wf_e₂. }
  intro x; destruct x as [|x]; simpl. 1:{ constructor. }
  specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?].
  eapply V_map_wf_val. 1:{ eassumption. } auto.
}

intros N'' HN'' v₁ v₂ Hv. 
specialize (He N'').
apply EnvRel_monotone with (N':=N'') in Hγ ; [|omega].
clear - Hv He Hγ. generalize N'', Hv, He, Hγ. clear N'' Hv He Hγ.

intros N Hv He Hγ.
apply ERel_monotone with (N := S N). 2:{ omega. }
eapply ERel_sss_l.
{ intros. constructor. }
eapply ERel_sss_r.
{ intros. constructor. }
repeat erewrite V_bind_bind_exp.
1:{
  eapply He with (γ₁ := env_ext γ₁ _) (γ₂ := env_ext γ₂ _).
  intro x. destruct x as [|x]; simpl.
  2:{ apply Hγ. }
  apply Hv.
}
+ intro x; destruct x as [ |x] ; simpl ; [reflexivity| ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
+ intro x; destruct x as [ |x] ; simpl ; [reflexivity| ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
Qed.

Lemma compat_val_fix T e₁ e₂ :
ERel_open (env_ext Γ (ty_fun ty_unit T)) T e₁ e₂ →
VRel_open Γ (ty_fun ty_unit T) (val_fix e₁) (val_fix e₂).
Proof.
intros [[Wf_e₁ Wf_e₂] He] N γ₁ γ₂ Hγ.
simpl V_bind_val.
simpl VRel.
split; [|split].
1:{
  constructor. eapply V_bind_wf_exp. 1:{ apply Wf_e₁. }
  intro x; destruct x as [|x]; simpl. 1:{ constructor. }
  specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?].
  eapply V_map_wf_val. 1:{ eassumption. } auto.
}
1:{
  constructor. eapply V_bind_wf_exp. 1:{ apply Wf_e₂. }
  intro x; destruct x as [|x]; simpl. 1:{ constructor. }
  specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?].
  eapply V_map_wf_val. 1:{ eassumption. } auto.
}
intros N'' HN'' v₁ v₂ Hv. destruct Hv ; subst.

apply EnvRel_monotone with (N':=N'') in Hγ ; [|omega].
clear- Wf_e₁ Wf_e₂ He Hγ. generalize He, Hγ. clear He Hγ.
induction N'' as [| N LoebIH ].
1:{ intros. apply ERel_O_nonval. intros. ktx_plug_is_val_absurd. }

intros He Hγ.
eapply ERel_sss_l.
{ intros. constructor. }
eapply ERel_sss_r.
{ intros. constructor. }
repeat erewrite V_bind_bind_exp.
1:{
  eapply He with (γ₁ := env_ext γ₁ _) (γ₂ := env_ext γ₂ _).
  intro x. destruct x as [|x]; simpl.
  2:{ specialize (Hγ x). eapply VRel_monotone ; [ apply Hγ | omega ]. }
  split; [|split].
  3:{
    intros N' HN' u₁ u₂ Hu; destruct Hu; subst.
    apply ERel_monotone with (N:=N); try omega.
    apply LoebIH.
    { apply He. }
    { eapply EnvRel_monotone; [ apply Hγ | omega ]. }
  }
  1:{
    constructor. eapply V_bind_wf_exp. 1:{ apply Wf_e₁. }
    intro x; destruct x as [|x]; simpl. 1:{ constructor. }
    specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?].
    eapply V_map_wf_val. 1:{ eassumption. } auto.
  }
  1:{
    constructor. eapply V_bind_wf_exp. 1:{ apply Wf_e₂. }
    intro x; destruct x as [|x]; simpl. 1:{ constructor. }
    specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?].
    eapply V_map_wf_val. 1:{ eassumption. } auto.
  }
}
{
  intro x; destruct x as [ |x] ; simpl ; [reflexivity| ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}
{
  intro x; destruct x as [ |x] ; simpl ; [reflexivity| ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}
Qed.

Lemma compat_val_unif :
VRel_open Γ (ty_dist ℝ) val_unif val_unif.
Proof.
intros N γ₁ γ₂ Hγ. simpl.
split; [|split]. 1:{ constructor. } 1:{ constructor. }
intros N' HN' K₁ K₂ HK.
destruct N' as [|N'].
1:{ apply ORel_O_nonval. intros. ktx_plug_is_val_absurd. }
apply KRel_monotone with (N' := N') in HK. 2:{ omega. }
assert (∀ r, ORel N' (ktx_plug K₁ (val_real r)) (ktx_plug K₂ (val_real r))) as HKr.
1:{ intro r. apply HK. 1:{ omega. } repeat eexists. }
clear- HKr.
split.
+ rewrite ktx_sample_unif_preserves_μNS.
  rewrite ktx_sample_unif_preserves_μNS_inf.
  apply integrand_extensionality_le. intro r.
  apply ennr_mult_le_compat_r.
  apply HKr.
+ intro V.
  rewrite ktx_sample_unif_preserves_μTV.
  rewrite ktx_sample_unif_preserves_μTV_sup.
  apply integrand_extensionality_le. intro r.
  apply ennr_mult_le_compat_r.
  apply HKr.
Qed.

End section_compat.

Section section_compat_val_query.
Context (V : Set).
Context (Γ : V → ty).
Context (T : ty).
Context (e₁ e₂ : exp V).

Lemma compat_val_query :
ERel_open Γ T e₁ e₂ →
T = ℝ ∨ T = ty_bool →
VRel_open Γ (ty_dist T) (val_query e₁) (val_query e₂).
Proof.
intros [[Wf_e₁ Wf_e₂] He] HT N γ₁ γ₂ Hγ.
simpl.
split; [|split].
1:{
  constructor. 2:{ apply HT. } eapply V_bind_wf_exp. 1:{ apply Wf_e₁. }
  intro x. specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?]. assumption.
}
1:{
  constructor. 2:{ apply HT. } eapply V_bind_wf_exp. 1:{ apply Wf_e₂. }
  intro x. specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?]. assumption.
}

intros N'' HN'' K₁ K₂ HK.
assert (ERel T N'' (V_bind_exp γ₁ e₁) (V_bind_exp γ₂ e₂)) as He'.
1:{ eapply He. eapply EnvRel_monotone ; [ apply Hγ | omega ]. }
assert (Wf_e₁' : wf_exp ∅→ (V_bind_exp γ₁ e₁) T).
1:{
  clear- Wf_e₁ Hγ. eapply V_bind_wf_exp. 1:{ apply Wf_e₁. }
  intro x. specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?]. assumption.
}
assert (Wf_e₂' : wf_exp ∅→ (V_bind_exp γ₂ e₂) T).
1:{
  clear- Wf_e₂ Hγ. eapply V_bind_wf_exp. 1:{ apply Wf_e₂. }
  intro x. specialize (Hγ x). apply VRel_wf_val in Hγ as [? ?]. assumption.
}
generalize N'', (V_bind_exp γ₁ e₁), (V_bind_exp γ₂ e₂),
  Wf_e₁', Wf_e₂', He', HK.
clear- HT.
intros N e₁ e₂ Wf_e₁ Wf_e₂ He HK.
apply He in HK as Obs_Ke ; [ | omega ].
destruct N as [|N].
1:{ apply ORel_O_nonval. intros. ktx_plug_is_val_absurd. }

assert (KRel T N ktx_hole ktx_hole) as Hhole.
1:{ 
  intros N' HN' v₁ v₂ Hv. simpl. clear- HT Hv.
  split.
  - rewrite μNS_val. apply μNS_inf_le_1.
  - intro. rewrite μTV_val.
    unfold μTV_sup. erewrite sup_of_constant.
    2:{ intro. rewrite μTV_val. reflexivity. }
    destruct HT; subst.
    { destruct Hv as [? [? ?]]; subst. apply ennr_le_refl. }
    { destruct Hv as [? [? ?]]; subst. apply ennr_le_refl. }
}
assert (ORel N (ktx_plug ktx_hole e₁) (ktx_plug ktx_hole e₂)) as Obs_e.
1:{ apply He ; [omega|]. apply Hhole. }
simpl in Obs_e.

apply ORel_monotone with (N' := N) in Obs_Ke. 2:{ omega. }
split.
2:{
  destruct (ennr_0_lt_dec (μNS_inf e₂)) as [NS_e₂|NS_e₂].
  + intro V. assert (0 < μNS N e₁) as NS_e₁.
    1:{ eapply ennr_lt_le_trans; [apply NS_e₂|]. apply Obs_e. }
    erewrite sss_preserves_μTV.
    2:{ intro. apply ktx_congruence. apply sss_sample_query. apply NS_e₁. }
    erewrite ktx_sample_query_preserves_μTV_sup by apply NS_e₂.
    cbn. apply ennr_mult_le_compat.
    - apply Obs_Ke.
    - apply ennr_mult_inv_le_compat. apply Obs_e.
  + intro V.
    assert (0 = μTV_sup e₂ V) as TV_e₂.
    1:{ apply ennr_le_0_is_0. rewrite NS_e₂. apply μTV_sup_le_μNS_inf. }
    assert (0 = μTV N e₁ V) as TV_e₁.
    1:{ apply ennr_le_0_is_0. rewrite TV_e₂. apply Obs_e. }
    assert (0 = μNS_inf (ktx_plug K₂ e₂)) as NS_K₂e₂.
    1:{ apply ennr_le_0_is_0. rewrite NS_e₂. apply μNS_inf_ktx_plug_le. }
    assert (0 = μTV_sup (ktx_plug K₂ e₂) V) as TV_K₂e₂.
    1:{ apply ennr_le_0_is_0. rewrite NS_K₂e₂. apply μTV_sup_le_μNS_inf. }
    destruct (ennr_0_lt_dec (μNS N e₁)) as [NS_e₁|NS_e₁].
    - erewrite sss_preserves_μTV.
      2:{ intro. apply ktx_congruence. apply sss_sample_query. assumption.  }
      cbn. replace (μTV N (ktx_plug K₁ e₁) V) with 0.
      1:{ rewrite ennr_mul_0_l. apply ennr_le_0. }
      apply ennr_le_0_is_0. rewrite TV_K₂e₂. apply Obs_Ke.
    - erewrite sss_preserves_μTV.
      2:{ intro. apply ktx_congruence. apply sss_sample_query_exn. assumption. }
      cbn. replace (μTV N (ktx_plug K₁ exp_exn) V) with 0.
      1:{ rewrite ennr_mul_0_l. apply ennr_le_0. } apply μTV_exn.
}

destruct (ennr_0_lt_dec (μNS N e₁)) as [NS_e₁|NS_e₁].
2:{
  erewrite sss_preserves_μNS.
  2:{ intro. apply ktx_congruence. apply sss_sample_query_exn; assumption. }
  erewrite <- μNS_exn. rewrite ennr_mul_1_r. apply μNS_inf_le_1.
}
erewrite sss_preserves_μNS.
2:{ intro. apply ktx_congruence. apply sss_sample_query; assumption. }
destruct (ennr_0_lt_dec (μNS_inf e₂)) as [NS_e₂|NS_e₂].
2:{
  assert (∀ V, 0 = μTV N e₁ V) as TV_e₁.
  1:{
    intro V. apply ennr_le_0_is_0. eapply ennr_le_trans. 1:{ apply Obs_e. }
    rewrite NS_e₂. apply μTV_sup_le_μNS_inf.
  }
  replace (μNS N (ktx_plug K₁ e₁)) with (μNS N e₁).
  1:{
    rewrite ennr_mult_inv_r_finite.
    + apply μNS_inf_le_1. + apply NS_e₁. + apply μNS_finite.
  }
  rewrite μNS_decompose. rewrite <-TV_e₁. rewrite ennr_add_0_l.
  rewrite μNS_ktx_rewrite. match goal with
    [ |- ?x = ?y + ?x ] => replace y with 0
  end.
  1:{ ring. }
  apply ennr_mult_infinity_compat_0_eq with (r2 := μTV N e₁ full_event).
  2:{ apply TV_e₁. }
  unfold μTV. rewrite <- integration_linear_mult_l.
  apply integrand_extensionality_le. intro t.
  rewrite <- ev2v_ρTV_same_weight. destruct (ev2v N t e₁) as [[[[? ?] ?] ?]|].
  2:{ apply ennr_le_0. }
  1:{ rewrite ennr_mul_comm. apply ennr_mult_le_compat_r. apply ennr_le_infinity. }
}

rewrite ktx_sample_query_preserves_μNS_inf by apply NS_e₂.
unfold μNS_inf.
setoid_rewrite μNS_decompose with (e := e₂).
setoid_rewrite μNS_decompose with (e := e₁).
setoid_rewrite μNS_ktx_rewrite.
repeat unshelve erewrite inf_is_lim'.
5:{ unfold antitone. intros. setoid_rewrite <-μNS_ktx_rewrite. apply μNS_antitone. omega. }
4:{ unfold antitone. intros. setoid_rewrite <- μNS_decompose. apply μNS_antitone. omega. }
2:{ apply antitone_has_lim. unfold antitone. intros. setoid_rewrite <- μNS_decompose. apply μNS_antitone. omega. }
1:{ apply antitone_has_lim. unfold antitone. intros. setoid_rewrite <-μNS_ktx_rewrite. apply μNS_antitone. omega. }
generalize_has_lim.
(* generalize dependent HasLim.
generalize dependent HasLim0.
setoid_rewrite μNS_decompose with (e := e₂).
setoid_rewrite μNS_decompose with (e := e₁).
setoid_rewrite μNS_ktx_rewrite. *)
repeat unshelve erewrite lim_of_sum.
4:{ apply μNT_has_lim. }
3:{ apply μTV_has_lim. }
2:{ apply μNT_has_lim. }
1:{
  replace (λ n, _) with (λ n, μNS n (ktx_plug K₂ e₂) - μNT n e₂ full_event).
  2:{
    clear. extensionality n. apply ennr_plus_minus.
    2:{ rewrite ennr_add_comm. apply μNS_ktx_rewrite. }
    rewrite μNS_ktx_rewrite. apply ennr_add_le_compat_2.
  }
  apply diff_has_lim.
  + intro. rewrite μNS_ktx_rewrite. apply ennr_add_le_compat_2.
  + apply μNS_has_lim.
  + apply μNT_has_lim.
}
apply ennr_inv_useful_fact.
5:{ rewrite <-μNS_decompose. apply μNS_finite. }
4:{
  unshelve erewrite <-lim_of_sum.
  1:{
    replace (λ n, _) with (λ n, μNS n e₂). 1:{ apply μNS_has_lim. }
    extensionality n. rewrite <-μNS_decompose. reflexivity.
  }
  match goal with [ |- context[lim ?f ?H] ] =>
    generalize H as HasLim'; intro HasLim'
  end.
  unshelve erewrite lim_extensionality.
  4:{ intro n. rewrite <-μNS_decompose. reflexivity. }
  1:{ apply μNS_has_lim. } generalize_has_lim.
  rewrite <-μNS_decompose.
  rewrite <-inf_is_lim'. 2:{ unfold antitone. apply μNS_antitone. }
  apply Obs_e.
}
2:{ apply νNS_le_μTV. }
1:{ apply lim_extensionality_le; intro n. apply νNS_le_μTV. }
generalize_has_lim.
match goal with [ |- _ ≤ _ - lim ?f ?H ] =>
  generalize H as HasLim4; intro HasLim4
end.
unfold μTV. unshelve erewrite <-lim_of_difference.
1:{
  apply diff_has_lim. 1:{ intro n. apply νNS_le_μTV. }
  + apply μTV_has_lim.
  + assumption.
}
2:{ intro n. apply νNS_le_μTV. }

specialize μTV_minus_νNS_pushforward_lim_μTVT as H.
unfold μTV, νNS, εNS in H. rewrite H with (WF_e := Wf_e₂). clear H.
specialize μTV_minus_νNS_pushforward_μTVT as H.
unfold μTV, νNS, εNS in H. eapply ennr_le_trans.
1:{ apply H with (WF_e := Wf_e₁). } clear H.
apply integrand_extensionality_le_meas.
+ intros [[v Wf_v]|].
  2:{ repeat rewrite ennr_minus_0. apply ennr_le_refl. }
  apply ennr_minus_le_compat_r.
  - apply μNS_le_1.
  - apply μNS_inf_le_1.
  - apply KRel_monotone with (N' := N) in HK. 2:{ omega. }
    apply HK. 1:{ omega. }
    (* Can this condition be included as an IH in the proof of the
    * fundamental lemma? I think so! *)
    destruct HT as [HT|HT]; subst; simpl.
    * inversion Wf_v. 1:{ auto. } repeat eexists.
    * inversion Wf_v. 1:{ auto. } repeat eexists.
+ intro VT.
  unfold μTVT_sup.
  setoid_rewrite μTVT_is_μTV.
  apply Obs_e.
Qed.
End section_compat_val_query.
