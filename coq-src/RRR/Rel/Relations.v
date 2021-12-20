Require Import RRR.Lebesgue.Lebesgue.
Require Import Omega.
Require Import RRR.Lang.Lang.
Import RRR.Lang.Syntax.
Require Import Lra.
Require Import Coq.Program.Wf.

Set Implicit Arguments.

Lemma loeb (P : nat → Prop) :
(∀ n, (∀ m, m < n → P m) → P n)%nat → ∀ n, P n.
Proof.
intros H n.
specialize (lt_wf n).
induction 1 as [ n _ H2 ].
apply H.
intros m Hm.
apply H2. apply Hm.
Qed.

Open Scope ennr_scope.

Definition ORel (N : nat) (e₁ e₂ : exp0) :=
μNS_inf e₂ ≤ μNS N e₁ ∧ ∀ V, μTV N e₁ V ≤ μTV_sup e₂ V.

Definition VRel_Sig := nat → val0 → val0 → Prop.

Definition KRel_fun (VRel : VRel_Sig)
(N : nat) (K₁ K₂ : ktx) :=
∀ N', N' <= N →
∀ v₁ v₂, VRel N' v₁ v₂ → ORel N' (ktx_plug K₁ v₁) (ktx_plug K₂ v₂).

Definition ERel_fun (VRel : VRel_Sig)
(N : nat) (e₁ e₂ : exp0) :=
∀ N', N' <= N →
∀ K₁ K₂, KRel_fun VRel N' K₁ K₂ → ORel N' (ktx_plug K₁ e₁) (ktx_plug K₂ e₂).

Fixpoint VRel (T : ty) (N : nat) (v₁ v₂ : val0) {struct T} : Prop :=
match T with
| ty_unit => v₁ = val_unit ∧ v₂ = val_unit
| ty_bool => ∃ b, v₁ = val_bool b ∧ v₂ = val_bool b
| ty_real => ∃ r, v₁ = val_real r ∧ v₂ = val_real r
| ty_fun U R =>
  wf_val ∅→ v₁ (ty_fun U R) ∧
  wf_val ∅→ v₂ (ty_fun U R) ∧
  ∀ (N' : nat), N' <= N →
  ∀ u₁ u₂, VRel U N' u₁ u₂ →
  ERel_fun (VRel R) N' (exp_app v₁ u₁) (exp_app v₂ u₂)
| ty_pair U W =>
  ∃ u₁ u₂ w₁ w₂, v₁ = val_pair u₁ w₁ ∧ v₂ = val_pair u₂ w₂ ∧
  VRel U N u₁ u₂ ∧ VRel W N w₁ w₂
| ty_dist T =>
  wf_val ∅→ v₁ (ty_dist T) ∧
  wf_val ∅→ v₂ (ty_dist T) ∧
  ERel_fun (VRel T) N (exp_sample v₁) (exp_sample v₂)
end.

Notation KRel T := (KRel_fun (VRel T)).
Notation ERel T := (ERel_fun (VRel T)).

Lemma ORel_monotone :
∀ e₁ e₂ N, ORel N e₁ e₂ →
∀ N', N' <= N →
ORel N' e₁ e₂.
Proof.
unfold ORel.
intros e₁ e₂ N O' N' HN'.
destruct O' as [O'NS O'TV].
split.
+ eapply ennr_le_trans; [apply O'NS; apply TV|].
  apply μNS_antitone. omega.
+ intro V. eapply ennr_le_trans; [|apply O'TV].
  apply μTV_monotone. omega.
Qed.

Lemma KRel_monotone T N K₁ K₂ :
KRel_fun T N K₁ K₂ →
∀ N', N' <= N →
KRel_fun T N' K₁ K₂.
Proof.
unfold KRel_fun.
intro H. intros. apply H.
+ omega.
+ assumption.
Qed.

Lemma ERel_monotone T N e₁ e₂ :
ERel_fun T N e₁ e₂ →
∀ N', N' <= N →
ERel_fun T N' e₁ e₂.
Proof.
unfold ERel_fun.
intro H. intros. apply H.
+ omega.
+ assumption.
Qed.

Lemma VRel_monotone :
∀ T N v₁ v₂,
VRel T N v₁ v₂ →
∀ N', N' <= N → VRel T N' v₁ v₂.
Proof.
induction T ; intros N v₁ v₂ Hv N' Hle ; simpl in Hv |- *.
+ assumption.
+ assumption.
+ assumption.
+ destruct Hv as [Wf_v₁ [Wf_v₂ Hv]].
  split; [|split]. 1:{ apply Wf_v₁. } 1:{ apply Wf_v₂. }
  intros N'' Hle' u₁ u₂ Hu. apply Hv.
  - omega.
  - apply Hu.
+ destruct Hv as [u₁ [u₂ [w₁ [w₂ [? [? [? ?]]]]]]].
  subst.
  repeat eexists ; eauto.
+ destruct Hv as [Wf_v₁ [Wf_v₂ Hv]].
  split; [|split]. 1:{ apply Wf_v₁. } 1:{ apply Wf_v₂. }
  eapply ERel_monotone ; eauto.
Qed.

Lemma ORel_sss_l N e₁ e₁' :
(∀ t, sss (eval N) t e₁ t e₁' 1) →
∀ e₂, ORel N e₁' e₂ →
ORel (S N) e₁ e₂.
Proof.
unfold ORel. intros Hsss e₂ O_N.
destruct O_N as [O_NS O_TV]. split.
+ erewrite sss_preserves_μNS by apply Hsss. rewrite ennr_mul_1_r.
  apply O_NS.
+ intro V. erewrite sss_preserves_μTV by apply Hsss.
  unfold unif_score_meas. rewrite ennr_mul_1_r. apply O_TV.
Qed.

Lemma ORel_sss_r N e₂ e₂' :
(∀ N₂ t, sss (eval N₂) t e₂ t e₂' 1) →
∀ e₁, ORel N e₁ e₂' →
ORel N e₁ e₂.
Proof.
unfold ORel.
intros Hsss e₁ O_N.
destruct O_N as [O_NS O_TV]. split.
+ erewrite sss_preserves_μNS_inf by apply Hsss.
  repeat rewrite ennr_mul_1_r.
  apply O_NS.
+ intros V. erewrite sss_preserves_μTV_sup by apply Hsss.
  simpl. rewrite ennr_mul_1_r. apply O_TV.
Qed.

Lemma ORel_O_nonval e₁ e₂ :
(∀ v, e₁ = exp_val v → False) →
ORel O e₁ e₂.
Proof.
intros NV.
split.
+ rewrite μNS_O. apply μNS_inf_le_1.
+ intro. rewrite μTV_O_nonval by apply NV. apply ennr_le_0.
Qed.

Lemma ERel_O_nonval T e₁ e₂ :
(∀ v, e₁ = exp_val v → False) →
ERel T O e₁ e₂.
Proof.
intros NV. intros N HN K₁ K₂ HK.
assert (N = O) by omega. subst.
apply ORel_O_nonval.
intros. ktx_plug_is_val_absurd. subst. eapply NV; eauto.
Qed.

Lemma ORel_stuck N₁ e₁ N₂ e₂ :
stop N₁ e₁ →
(∀ v, e₁ = exp_val v → False) →
stop N₂ e₂ →
(∀ v, e₂ = exp_val v → False) →
∀ N, ORel N e₁ e₂.
Proof.
intros Stop_e₂ NV_e₂ Stop_e₁ NV_e₁.
split.
+ erewrite <- μNS_inf_stuck by eassumption. apply ennr_le_0.
+ intro. erewrite <- μTV_stuck by eassumption. apply ennr_le_0.
Qed.

Lemma ERel_stuck N₁ e₁ N₂ e₂ :
stop N₁ e₁ →
(∀ v, e₁ = exp_val v → False) →
stop N₂ e₂ →
(∀ v, e₂ = exp_val v → False) →
∀ T N, ERel T N e₁ e₂.
Proof.
intros Stop₁ NV₁ Stop₂ NV₂ T N.
intros N' HN K₁ K₂ HK.
eapply ORel_stuck.
4:{ intros. ktx_plug_is_val_absurd. subst. eapply NV₂. reflexivity. }
3:{ apply ktx_preserves_stuck; eassumption. }
2:{ intros. ktx_plug_is_val_absurd. subst. eapply NV₁. reflexivity. }
1:{ apply ktx_preserves_stuck; eassumption. }
Qed.

Lemma ERel_exn T N :
ERel T N exp_exn exp_exn.
Proof.
intros N' HN' K₁ K₂ HK. split.
+ rewrite <-μNS_exn. apply μNS_inf_le_1.
+ intro. rewrite <-μTV_exn. apply ennr_le_0.
Qed.

Lemma ERel_sss_l T N e₁ e₁' :
(∀ N', N' <= N → ∀ t, sss (eval N') t e₁ t e₁' 1) →
∀ e₂, ERel T N e₁' e₂ →
ERel T (S N) e₁ e₂.
Proof.
intros Hsss e₂ He N' HN' K₁ K₂ HK.
destruct N'.
+ apply ORel_O_nonval.
  intros v Hv. ktx_plug_is_val_absurd. subst.
  specialize (Hsss N (le_refl _) entropy0).
  inversion Hsss.
+ apply ORel_sss_l with (e₁' := ktx_plug K₁ e₁').
  1:{ intro t. apply ktx_congruence. apply Hsss ; omega. }
  apply He. 1:{ omega. }
  eapply KRel_monotone ; [ apply HK | omega ].
Qed.

Lemma ERel_sss_r T N e₂ e₂' :
(∀ N₂ t, sss (eval N₂) t e₂ t e₂' 1) →
∀ e₁, ERel T N e₁ e₂' →
ERel T N e₁ e₂.
Proof.
intros Hsss e₁ He N' HN' K₁ K₂ HK.
apply He in HK as Obs ; [|omega].
eapply ORel_sss_r with (e₂' := ktx_plug K₂ e₂').
+ intros N₂ t. apply ktx_congruence. apply Hsss.
+ apply Obs.
Qed.

Lemma VRel_in_ERel T v₁ v₂ N :
VRel T v₁ v₂ N →
ERel T v₁ v₂ N.
Proof.
intro Hv.
intros N' Hle K₁ K₂ HK.
apply HK ; [ omega | ].
eapply VRel_monotone ; eauto.
Qed.

Lemma ERel_ktx_plug Ta Tb N K₁ K₂ :
( ∀ N', N' <= N →
  ∀ v₁ v₂, VRel Ta N' v₁ v₂ →
  ERel Tb N' (ktx_plug K₁ v₁) (ktx_plug K₂ v₂) ) →
∀ N', N' <= N →
∀ e₁ e₂, ERel Ta N' e₁ e₂ →
ERel Tb N' (ktx_plug K₁ e₁) (ktx_plug K₂ e₂).
Proof.
intros HKv N' Hle' e₁ e₂ He.
intros N'' Hle'' J₁ J₂ HJ.
repeat rewrite ktx_plug_comp.
apply He ; [ apply Hle'' | ].
intros N''' Hle''' v₁ v₂ Hv.
repeat rewrite <- ktx_plug_comp.
specialize (HKv N''').
eapply HKv ; [ omega | | omega | ].
+ eapply VRel_monotone ; [ eassumption | omega ].
+ eapply KRel_monotone ; [ eassumption | omega ].
Qed.

Lemma VRel_wf_val T N v₁ v₂ :
VRel T N v₁ v₂ → wf_val ∅→ v₁ T ∧ wf_val ∅→ v₂ T.
Proof.
generalize N v₁ v₂. clear. induction T; intros N v₁ v₂ Hv.
+ destruct Hv. subst. split; constructor.
+ destruct Hv as [? [? ?]]. subst. split; constructor.
+ destruct Hv as [? [? ?]]. subst. split; constructor.
+ destruct Hv as [? [? ?]]. split; assumption.
+ destruct Hv as [? [? [? [? [? [? [? ?]]]]]]]. subst.
  apply IHT1 in H1 as [? ?].
  apply IHT2 in H2 as [? ?].
  split; constructor; assumption.
+ destruct Hv as [? [? ?]]. split; assumption.
Qed.

Section section_open_rels.
Context (V : Set).
Context (Γ : V → ty).

Definition EnvRel N (γ₁ γ₂ : V → val0) :=
∀ x, VRel (Γ x) N (γ₁ x) (γ₂ x).

Definition VRel_open (T : ty) (v₁ v₂ : val V) :=
∀ N,
∀ γ₁ γ₂, EnvRel N γ₁ γ₂ →
VRel T N (V_bind_val γ₁ v₁) (V_bind_val γ₂ v₂).

Definition ERel_open (T : ty) (e₁ e₂ : Syntax.exp V) :=
(wf_exp Γ e₁ T ∧ wf_exp Γ e₂ T) ∧
∀ N,
∀ γ₁ γ₂, EnvRel N γ₁ γ₂ →
         ERel T N (V_bind_exp γ₁ e₁) (V_bind_exp γ₂ e₂).
    
Lemma EnvRel_monotone N γ₁ γ₂ :
EnvRel N γ₁ γ₂ →
∀ N', N' <= N → EnvRel N' γ₁ γ₂.
Proof.
intros Hγ N' Hle x.
eapply VRel_monotone.
+ apply Hγ.
+ omega.
Qed.

Lemma EnvRel_wf_env N γ₁ γ₂ :
EnvRel N γ₁ γ₂ → wf_env γ₁ Γ ∧ wf_env γ₂ Γ.
Proof.
intro Hγ.
assert (∀ x, wf_val ∅→ (γ₁ x) (Γ x) ∧ wf_val ∅→ (γ₂ x) (Γ x)).
2:{ split; intro; apply H. }
intro x. eapply VRel_wf_val. apply Hγ.
Qed.

End section_open_rels.

Definition Ciu N e₁ e₂ :=
∀ K, ORel N (ktx_plug K e₁) (ktx_plug K e₂).

Definition Ciu_open (V: Set) (Γ : V → ty) (T : ty) (e₁ e₂ : exp V) :=
(wf_exp Γ e₁ T ∧ wf_exp Γ e₂ T) ∧
∀ N γ, wf_env γ Γ → Ciu N (V_bind_exp γ e₁) (V_bind_exp γ e₂).

Lemma ERel_Ciu_ERel_open (V: Set) (Γ : V → ty) T e₁ e₂' e₂ :
ERel_open Γ T e₁ e₂' →
Ciu_open Γ T e₂' e₂ →
ERel_open Γ T e₁ e₂.
Proof.
intros HE HC.
destruct HE as [[? ?] HE].
destruct HC as [[? ?] HC].
split. 1:{ split; assumption. }
intros N γ₁ γ₂ Hγ.
intros N' HN' K₁ K₂ HK.
apply EnvRel_wf_env in Hγ as Wf_γ. destruct Wf_γ as [Wf_γ₁ Wf_γ₂].

specialize (HE N γ₁ γ₂ Hγ).
apply HE in HK as Obs' ; [|omega].
destruct Obs' as [Obs' Obs''].
assert (∀ M, μNS_inf (ktx_plug K₂ (V_bind_exp γ₂ e₂)) ≤ μNS M (ktx_plug K₂ (V_bind_exp γ₂ e₂'))) as NS_e₂'.
1:{
  clear -HC Wf_γ₂. intro M.
  specialize (HC M γ₂ Wf_γ₂ K₂) as [HC _]. apply HC.
}
assert (∀ A M, μTV M (ktx_plug K₂ (V_bind_exp γ₂ e₂')) A ≤ μTV_sup (ktx_plug K₂ (V_bind_exp γ₂ e₂)) A) as TV_e₂'.
1:{
  clear -HC Wf_γ₂. intros A M.
  specialize (HC M γ₂ Wf_γ₂ K₂) as [_ HC]. apply HC.
}

apply μNS_inf_is_glb in NS_e₂'.
split.
+ eapply ennr_le_trans; [apply NS_e₂'|apply Obs'].
+ intro A. eapply ennr_le_trans; [apply Obs''|].
  eapply μTV_sup_is_lub in TV_e₂'. apply TV_e₂'.
Qed.
