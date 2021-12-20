Require Import Coq.Reals.Reals.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Minus.
Require Import Coq.micromega.Lra.
Require Import RRR.Lang.Syntax.
Require Import RRR.Lang.Bindings.
Require Import RRR.Lang.BindingsFacts.
Require Import RRR.Lang.Entropy.
Require Import RRR.Lang.SmallStep.
Require Import RRR.Lang.Evaluation.
Require Import RRR.Lebesgue.Lebesgue.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition μNS_inf := λ e, inf (λ N, μNS N e).

(** The value measure induced by [ρTV] *)
Definition μTV (N : nat) (e : exp0) : Meas val0 :=
λ V, ∫ (λ t, ρTV N t e V) μentropy.

Definition μTV_sup := λ e V, sup (λ N, μTV N e V).

(** The measure induced by [ρNT] *)
Definition μNT (N : nat) (e : exp0) : Meas val0 :=
λ V, ∫ (λ t, ρNT N t e V) μentropy.

Lemma ρNS_decompose (N : nat) (t : entropy) (e : exp0) :
ρNS N t e = ρTV N t e full_event + ρNT N t e full_event.
Proof.
unfold ρNS, ρTV, ρNT.
destruct (eval N t e) as [ [[t' e'] w] | ].
2:{ ring. }
destruct e'; cbn; ring.
Qed.

Lemma μNS_decompose (N : nat) (e : exp0) :
μNS N e = μTV N e full_event + μNT N e full_event.
Proof.
unfold μNS, μTV, μNT.
rewrite integration_linear_plus.
integrand_extensionality t.
apply ρNS_decompose.
Qed.

Lemma ρTV_monotone_in_V (V' V : Event val0) :
(∀ v, if V' v then V v = true else True) →
∀ N t e, ρTV N t e V' ≤ ρTV N t e V.
Proof.
intros HV N t e.
unfold ρTV.
repeat match goal with
| [ |- context[match ?x with _ => _ end] ] =>
  match type of x with
  | bool => destruct x eqn:?
  | _ => destruct x
  end
| [ |- ?x ≤ ?x ] => apply ennr_le_refl
| [ |- _ * ?x ≤ _ * ?x ] => apply ennr_mult_le_compat_r
| [ |- 0 ≤ _ ] => apply ennr_le_0
end.
unfold indicator.
specialize (HV v) ; destruct (V' v) eqn:? ; crush.
Qed.

Lemma μNT_monotone_in_V (V' V : Event val0) :
(∀ v, if V' v then V v = true else True) →
∀ N e, μTV N e V' ≤ μTV N e V.
Proof.
intros HV N e.
unfold μNT.
apply integrand_extensionality_le ; intro t.
apply ρTV_monotone_in_V ; apply HV.
Qed.

Lemma ρTV_le_full_event N t e V :
ρTV N t e V ≤ ρTV N t e full_event.
Proof.
apply ρTV_monotone_in_V.
intro v. destruct (V v); reflexivity.
Qed.

Lemma μTV_le_full_event N e V :
μTV N e V ≤ μTV N e full_event.
Proof.
apply integrand_extensionality_le.
intro; apply ρTV_le_full_event.
Qed.

Lemma μTV_le_μNS N e V :
μTV N e V ≤ μNS N e.
Proof.
eapply ennr_le_trans ; [ apply μTV_le_full_event |].
rewrite μNS_decompose. apply ennr_add_le_compat_1.
Qed.

Lemma μNT_le_μNS N e :
μNT N e full_event ≤ μNS N e.
Proof.
rewrite μNS_decompose. apply ennr_add_le_compat_2.
Qed.

Lemma μNT_as_diff N e :
μNT N e full_event = μNS N e - μTV N e full_event.
Proof.
apply eq_sym.
apply ennr_plus_minus. 2:{ apply μNS_decompose. }
apply μTV_le_μNS.
Qed.

Lemma μNS_inf_le e C N : μNS N e ≤ C → μNS_inf e ≤ C.
Proof.
intro NS. unfold μNS_inf.
specialize (inf_is_glb (λ N, μNS N e)) as H.
destruct H as [H _]. unfold is_lower_bound in H.
eapply ennr_le_trans. 2:{ apply NS. }
apply H. repeat eexists.
Qed.

Lemma μNS_inf_le_μNS e N : μNS_inf e ≤ μNS N e.
Proof.
  eapply μNS_inf_le. unfold ennr_le. auto.
Qed.

Lemma μTV_sup_ge_μTV e N A : μTV N e A ≤ μTV_sup e A.
Proof.
  unfold μTV_sup. pose proof sup_is_lub. specialize H with (λ N0 : nat, μTV N0 e A).
  destruct H. unfold is_upper_bound in H. specialize H with (μTV N e A).
  eapply H. exists N. reflexivity.
Qed.

Lemma μNS_inf_is_glb e C :
(∀ N, C ≤ μNS N e) →
C ≤ μNS_inf e.
Proof.
intro H. unfold μNS_inf.
specialize (inf_is_glb (λ N, μNS N e)) as Q.
destruct Q as [_ Q]. apply Q.
unfold is_lower_bound. intros r [n Hr]. subst r. apply H.
Qed.

Lemma μTV_sup_is_lub e V C :
(∀ N, μTV N e V ≤ C) →
μTV_sup e V ≤ C.
Proof.
intro H. unfold μTV_sup.
specialize (sup_is_lub (λ N, μTV N e V)) as Q.
destruct Q as [_ Q]. apply Q.
unfold is_lower_bound. intros r [n Hr]. subst r. apply H.
Qed.

Section section_eval_weight_positive_finite_aux.
Context (N: nat).
Context (eval_weight_positive_finite :
  ∀ t e t' e' w,
  eval N t e = Some (t', e', w) → 0 < w < ∞).

Fact ρNS_finite_aux t e : ρNS_aux (eval N) t e < ∞.
Proof.
unfold ρNS_aux.
destruct (eval N t e) as [ [[t' e'] w] | ] eqn:Heval.
2:{ simpl; lra. }
apply eval_weight_positive_finite in Heval.
destruct Heval; assumption.
Qed.

Fact μNS_finite_aux e : μNS_aux (eval N) e < ∞.
Proof.
unfold μNS_aux.
apply ennr_lt_le_trans with (r2 := ∫ (λ t, ∞) μentropy).
2:{
  setoid_rewrite integration_of_const; try reflexivity.
  rewrite μentropy_is_a_probability_measure.
  rewrite ennr_mul_comm, ennr_mul_1_l.
  apply ennr_le_refl.
}
apply integrand_extensionality_lt.
intro; apply ρNS_finite_aux.
Qed.

Fact sss_weight_positive_finite_aux t e t' e' w :
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w  → 0 < w < ∞.
Proof.
induction 1;
try match goal with
| [ |- 0 < 1 < ∞ ] =>
  split; simpl; lra
| [ H : ?P |- ?P ] => exact H
end.
+ apply ennr_inv_0_lt_finite_compat. 2:{ apply μNS_finite_aux. }
  assumption.
+ simpl; auto.
Qed.
End section_eval_weight_positive_finite_aux.

Lemma eval_weight_positive_finite N : ∀ t e t' e' w,
eval N t e = Some (t', e', w) → 0 < w < ∞.
Proof.
induction N as [ | N IHN ]; do 5 intro.
+ simpl eval.
  intro H ; inversion H ; subst ; clear H.
  simpl ; split ; lra.
+ intro eval_S.
  apply unfold_eval_S_to_Some in eval_S.
  destruct eval_S as [ 
    [ [v [? [? ?]]] | [K [? [? ?]]] ] |
    [t''[e''[w'[Hsss[w''[Hw Heval]]]]]]
  ].
  1:{ subst. simpl; split; lra. }
  1:{ subst. simpl; split; lra. }
  1:{
    subst.
    apply sss_weight_positive_finite_aux in Hsss; [ | apply IHN ].
    apply IHN in Heval.
    apply ennr_mult_0_lt_and_finite; assumption.
  }
Qed.

Lemma sss_weight_positive_finite N t e t' e' w :
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w → 0 < w < ∞.
Proof.
eapply sss_weight_positive_finite_aux; try eassumption.
apply eval_weight_positive_finite.
Qed.

Corollary sss_weight_finite N t e t' e' w :
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w → w < ∞.
Proof.
intro H; apply sss_weight_positive_finite in H. crush.
Qed.

Corollary sss_weight_positive N t e t' e' w :
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w → 0 < w.
Proof.
intro H; apply sss_weight_positive_finite in H. crush.
Qed.

Lemma μNS_finite N e : μNS N e < ∞.
Proof.
apply μNS_finite_aux.
apply eval_weight_positive_finite.
Qed.

Lemma μNS_inf_finite : ∀ e, μNS_inf e < ∞.
Proof.
  intro e.
  eapply ennr_le_lt_trans.
  apply μNS_inf_le_μNS.
  apply μNS_finite.
  Unshelve. exact 0%nat.
Qed.

Lemma μTV_O_val v V :
μTV O (exp_val v) V = if V v then 1 else 0.
Proof.
destruct (V v) eqn:Hv.
+ unfold μTV.
  replace 1 with (μentropy full_event).
  2:{ rewrite μentropy_is_a_probability_measure ; reflexivity. }
  rewrite <- integration_of_indicator.
  unfold indicator.
  integrand_extensionality t.
  cbn.
  unfold indicator, const.
  rewrite Hv ; cbn ; ring.
+ unfold μTV. 
  erewrite <- integration_of_0.
  integrand_extensionality t.
  cbn.
  unfold indicator, const.
  rewrite Hv ; cbn ; ring.
Qed.

Lemma μTV_S_val N (v : val0) V :
μTV (S N) v V = μTV N v V.
Proof.
unfold μTV.
integrand_extensionality t.
unfold ρTV.
rewrite eval_val_S.
destruct N ; simpl ; ring.
Qed.

Lemma μTV_val N v V :
μTV N (exp_val v) V = if V v then 1 else 0.
Proof.
induction N.
+ apply μTV_O_val.
+ rewrite μTV_S_val ; apply IHN.
Qed.

Lemma ρNT_O_val t v V : ρNT O t (exp_val v) V = if V v then 0 else 1.
Proof.
cbn.
destruct (V v) ; ring.
Qed.

Lemma μNT_O_val v V : μNT O (exp_val v) V = if V v then 0 else 1.
Proof.
destruct (V v) eqn:Hv.
+ erewrite <- integration_of_0.
  integrand_extensionality t.
  rewrite ρNT_O_val, Hv; ring.
+ rewrite <- μentropy_is_a_probability_measure.
  rewrite <- ennr_mul_1_l.
  erewrite <- integration_of_const.
  - integrand_extensionality t.
    reflexivity.
  - intro; simpl.
    rewrite ρNT_O_val, Hv; ring.
Qed.

Lemma ρNT_S_val N t v : ρNT (S N) t (exp_val v) full_event = 0.
Proof.
cbn; ring.
Qed.

Lemma μNT_S_val N v : μNT (S N) (exp_val v) full_event = 0.
Proof.
erewrite <- integration_of_0.
integrand_extensionality t.
apply ρNT_S_val.
Qed.

Lemma μNT_val N v : μNT N (exp_val v) full_event = 0.
Proof.
destruct N.
+ apply μNT_O_val.
+ apply μNT_S_val.
Qed.

Lemma μNS_val N v : μNS N (exp_val v) = 1.
Proof.
rewrite μNS_decompose.
rewrite μTV_val, μNT_val.
cbn; ring.
Qed.

Lemma μNS_inf_val v : μNS_inf (exp_val v) = 1.
Proof.
  unfold μNS_inf.
  apply inf_of_constant.
  intro n.
  apply μNS_val.
Qed.

Lemma ρTV_O_nonval t e V : (∀ v, e = exp_val v → False) → ρTV O t e V = 0.
Proof.
intro H.
unfold ρTV.
destruct (eval 0 t e) as [ [[t' e'] w] | ] eqn:Heval.
+ unfold ρTV.
  simpl eval in Heval |- *.
  inversion Heval ; subst ; clear Heval.
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | [ |- ?x = ?x ] => reflexivity
  end.
  exfalso ; eapply H ; reflexivity.
+ unfold ρTV.
  simpl eval in Heval.
  inversion Heval.
Qed.

Lemma μTV_O_nonval e V : (∀ v, e = exp_val v → False) → μTV O e V = 0.
Proof.
intro H.
unfold μTV.
erewrite <- integration_of_0.
integrand_extensionality t.
apply ρTV_O_nonval ; apply H.
Qed.

Lemma μTV_stuck_S N e V :
stop N e →
(∀ v, e = exp_val v → False) →
0 = μTV (S N) e V.
Proof.
intros Hstop e_not_val.
replace 0 with (0 * μentropy full_event) ; [ | ring ].
erewrite <- integration_of_const with (f := λ _, 0) ; [ | intro ; ring ].
integrand_extensionality t.
unfold ρTV.
simpl eval.
destruct (exp_val_dec e) as [ [v Hv] | ].
1:{ subst; exfalso. eapply e_not_val. reflexivity. }
destruct (exp_ktx_exn_dec e) as [ [K ?] | ].
1:{
  subst. destruct (ktx_plug K exp_exn); try ring.
  exfalso. eapply e_not_val. reflexivity.
}
destruct (sss_det (eval N) t e) as [ [?[?[?[? ?]]]] |]; [| ring ].
exfalso.
destruct Hstop as [Sss_False _].
specialize (Sss_False t).
eapply Sss_False.
eassumption.
Qed.

Lemma μNS_stuck N e :
stop N e →
(∀ v, e = exp_val v → False) →
0 = (μNS (S N)) e.
Proof.
intros Hstop e_not_val.
replace 0 with (0 * μentropy full_event) ; [ | ring ].
erewrite <- integration_of_const with (f := λ _, 0) ; [ | intro ; ring ].
integrand_extensionality t.
unfold ρNS.
simpl eval.
destruct (exp_val_dec e) as [ [v Hv] | ].
1:{ subst; exfalso. eapply e_not_val. reflexivity. }
destruct Hstop as [e_stuck e_not_exn].
destruct (exp_ktx_exn_dec e) as [ [K ?] | ].
1:{ exfalso. eapply e_not_exn. eassumption. }
destruct (sss_det (eval N) t e) as [ [?[?[?[? ?]]]] |]; [| ring ].
exfalso.
specialize (e_stuck t).
eapply e_stuck.
eassumption.
Qed.

Lemma μNS_inf_stuck N e :
stop N e →
(∀ v, e = exp_val v → False) →
0 = μNS_inf e.
Proof.
intros Stop Notval_e.
apply ennr_le_antisym. 1:{ apply ennr_le_0. }
eapply μNS_inf_le with (N := S N).
erewrite μNS_stuck by eassumption.
apply ennr_le_refl.
Qed.

Lemma ρNT_O_nonval t e V : (∀ v, e = exp_val v → False) → ρNT O t e V = 1.
Proof.
intro H.
unfold ρNT.
destruct (eval 0 t e) as [ [[t' e'] w] | ] eqn:Heval.
+ simpl eval in Heval.
  inversion Heval ; subst ; clear Heval.
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | [ |- ?x = ?x ] => reflexivity
  end.
  exfalso ; eapply H ; reflexivity.
+ simpl eval in Heval.
  inversion Heval.
Qed.

Lemma μNT_O_nonval e V : (∀ v, e = exp_val v → False) → μNT O e V = 1.
Proof.
intro H.
replace 1 with (μentropy full_event).
2:{ rewrite μentropy_is_a_probability_measure ; reflexivity. }
unfold μNT.
replace (μentropy full_event) with (1 * μentropy full_event).
2:{ rewrite ennr_mul_1_l ; reflexivity. }
erewrite <- integration_of_const.
2:{ reflexivity. }
integrand_extensionality t.
apply ρNT_O_nonval ; apply H.
Qed.

Lemma μNS_O_nonval e : (∀ v, e = exp_val v → False) → μNS O e = 1.
Proof.
intro H.
rewrite μNS_decompose.
rewrite μTV_O_nonval, μNT_O_nonval; try assumption.
ring.
Qed.

Lemma μNS_O e : μNS O e = 1.
Proof.
destruct (exp_val_dec e) as [[v Hv] | ]; [subst | ].
+ apply μNS_val.
+ apply μNS_O_nonval. assumption.
Qed.

Lemma μTV_exn N K V : 0 = μTV N (K[/exp_exn]) V.
Proof.
unfold μTV. rewrite integration_const_entropy with (v := 0). 1:{ ring. }
intro t. apply eq_sym. apply ρTV_exn.
Qed.

Lemma μNT_exn N K V : 1 = μNT N (K[/exp_exn]) V.
Proof.
unfold μNT. rewrite integration_const_entropy with (v := 1). 1:{ ring. }
intro t. apply eq_sym. apply ρNT_exn.
Qed.

Lemma ρNS_exn N t K : 1 = ρNS N t (K[/exp_exn]).
Proof.
unfold ρNS. rewrite eval_ktx_exn. reflexivity.
Qed.

Lemma μNS_exn N K : 1 = μNS N (K[/exp_exn]).
Proof.
unfold μNS. rewrite integration_const_entropy with (v := 1). 1:{ ring. }
intro t. apply eq_sym. apply ρNS_exn.
Qed.

Lemma sss_preserves_ρTV N t t' e e' w:
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w →
∀ V, ρTV (S N) t e V = (ρTV N t' e' V) * w.
Proof.
intros Hsss V.
apply sss_eval in Hsss.
unfold ρTV.
rewrite Hsss.
destruct (eval N t' e') as [[[T E] W] | ] ; [ | ring ].
repeat match goal with
| [ |- context[ match ?x with _ => _ end ] ] => destruct x
end ; ring.
Qed.

Lemma sss_preserves_μTV N e e' w:
(∀ t, (eval N) ⟨t|e⟩ ⤳ ⟨t|e'⟩ • w ) →
∀ V, μTV (S N) e V = unif_score_meas w (μTV N e') V.
Proof.
intros Hsss V.
unfold μTV.
simpl unif_score_meas.
rewrite <- integration_linear_mult_r.
integrand_extensionality t.
apply sss_preserves_ρTV ; apply Hsss.
Qed.

Lemma sss_preserves_ρNT N t e t' e' w:
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w →
∀ V, ρNT (S N) t e V = (ρNT N t' e' V) * w.
Proof.
intros Hsss V.
apply sss_eval in Hsss.
unfold ρNT.
rewrite Hsss.
destruct (eval N t' e') as [[[T E] W] | ] ; [ | ring ].
repeat match goal with
| [ |- context[ match ?x with _ => _ end ] ] => destruct x
end ; ring.
Qed.

Lemma sss_preserves_μNT N e e' w:
(∀ t, (eval N) ⟨t|e⟩ ⤳ ⟨t|e'⟩ • w) →
∀ V, μNT (S N) e V = unif_score_meas w (μNT N e') V.
Proof.
intros Hsss V.
unfold μNT.
simpl unif_score_meas.
rewrite <- integration_linear_mult_r.
integrand_extensionality t.
eapply sss_preserves_ρNT ; apply Hsss.
Qed.

Lemma sss_preserves_ρNS N t e t' e' w:
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w →
ρNS (S N) t e = (ρNS N t' e') * w.
Proof.
intro Hsss.
apply sss_eval in Hsss.
unfold ρNS.
rewrite Hsss.
destruct (eval N t' e') as [[[T E] W] | ] ; [ | ring ].
repeat match goal with
| [ |- context[ match ?x with _ => _ end ] ] => destruct x
end ; ring.
Qed.

Lemma sss_preserves_μNS N e e' w:
(∀ t, (eval N) ⟨t|e⟩ ⤳ ⟨t|e'⟩ • w) →
μNS (S N) e = (μNS N e') * w.
Proof.
intros Hsss.
unfold μNS.
rewrite <- integration_linear_mult_r.
integrand_extensionality t.
eapply sss_preserves_ρNS ; apply Hsss.
Qed.

Lemma ktx_sample_unif_preserves_μTV N K V:
μTV (S N) (K[/(exp_sample val_unif)]) V =
∫ (λ r, μTV N (K[/val_real r]) V * if (Rinterval_dec 0 1 r) then 1 else 0) lebesgue_measure.
Proof.
unfold μTV.
rewrite <- integration_πU_lebesgue.
replace (λ t, ρTV (S N) t (K[/exp_sample val_unif]) V)
  with (λ t, ρTV N (πR t) (K[/val_real (πU t)]) V).
2:{
  extensionality t.
  erewrite sss_preserves_ρTV with (w := 1).
  1:{ rewrite ennr_mul_1_r; reflexivity. }
  apply ktx_congruence.
  apply sss_sample_unif.
}
setoid_rewrite <- integration_πL_πR.
reflexivity.
Qed.

Lemma sample_unif_preserves_μTV N V:
μTV (S N) (exp_sample val_unif) V =
∫ (λ r, μTV N (val_real r) V * if (Rinterval_dec 0 1 r) then 1 else 0) lebesgue_measure.
Proof.
assert (∀ e, e = ktx_hole[/e]) as H by trivial.
setoid_rewrite H. 
apply ktx_sample_unif_preserves_μTV.
Qed.

Lemma ktx_sample_unif_preserves_μNT N K V :
μNT (S N) (K[/exp_sample val_unif]) V =
∫ (λ r, μNT N (K[/val_real r]) V * if (Rinterval_dec 0 1 r) then 1 else 0) lebesgue_measure.
Proof.
unfold μNT.
rewrite <- integration_πU_lebesgue.
replace (λ t, ρNT (S N) t (K[/exp_sample val_unif]) V)
  with (λ t, ρNT N (πR t) (K[/val_real (proj1_sig (πL t 0%nat))]) V).
2:{
  extensionality t.
  erewrite sss_preserves_ρNT with (w := 1).
  1:{ rewrite ennr_mul_comm, ennr_mul_1_l; reflexivity. }
  apply ktx_congruence.
  apply sss_sample_unif.
}
setoid_rewrite <- integration_πL_πR.
reflexivity.
Qed.

Lemma sample_unif_preserves_μNT N V:
μNT (S N) (exp_sample val_unif) V =
∫ (λ r, μNT N (val_real r) V * if (Rinterval_dec 0 1 r) then 1 else 0) lebesgue_measure.
Proof.
assert (∀ e, e = ktx_hole[/e]) as H by trivial.
setoid_rewrite H. 
apply ktx_sample_unif_preserves_μNT.
Qed.

Lemma ktx_sample_unif_preserves_μNS N K :
μNS (S N) (K[/exp_sample val_unif]) =
∫ (λ r, μNS N (K[/val_real r]) * if (Rinterval_dec 0 1 r) then 1 else 0) lebesgue_measure.
Proof.
unfold μNS.
rewrite <- integration_πU_lebesgue.
replace (λ t, ρNS (S N) t (K[/exp_sample val_unif]))
  with (λ t, ρNS N (πR t) (K[/val_real (proj1_sig (πL t 0%nat))])).
2:{
  extensionality t.
  erewrite sss_preserves_ρNS with (w := 1).
  1:{ rewrite ennr_mul_comm, ennr_mul_1_l; reflexivity. }
  apply ktx_congruence.
  apply sss_sample_unif.
}
setoid_rewrite <- integration_πL_πR.
reflexivity.
Qed.

Lemma sample_unif_preserves_μNS N :
μNS (S N) (exp_sample val_unif) =
∫ (λ r, μNS N (val_real r) * if (Rinterval_dec 0 1 r) then 1 else 0) lebesgue_measure.
Proof.
assert (∀ e, e = ktx_hole[/e]) as H by trivial.
setoid_rewrite H. 
apply ktx_sample_unif_preserves_μNS.
Qed.

Lemma ev2v_None_then_ρNS_Ke_is_ρNT_e N : ∀ t K e,
ev2v N t e = None →
(ρNS N) t (K[/e]) = ρNT N t e full_event.
Proof.
induction N as [|N IHN]; do 3 intro; intro H.
1:{
  cbn in H |- *.
  destruct (exp_val_dec e) as [[u ?]|Notval_e] eqn:Dec_val_e; inversion H; subst.
  destruct e; try ring; try inversion Dec_val_e.
}
destruct (exp_val_dec e) as [[u ?]|Notval_e] eqn:Dec_val_e.
1:{ subst. cbn in H. inversion H. }
unfold ρNS. unfold ρNT.
apply ev2v_None_eval in H as [Q | [? [e' [? [Q Notval_e']]]]]; rewrite Q.
+ rewrite eval_None_ktx_plug by assumption. ring.
+ erewrite eval_Some_ktx_plug by eassumption. cbn.
  destruct e'; try reflexivity.
  1:{ exfalso. eapply Notval_e'. reflexivity. }
Qed.

(** * Helper densities *)

Definition ρNS_ktx N t K e :=
match ev2v N t e with
| Some (k, t', v, w) => w * ρNS (N - k)%nat t' (K[/v])
| None => ρNT N t e full_event
end.

Lemma ρNS_ktx_rewrite (N : nat) (t : entropy) (K : ktx) (e : exp0) :
ρNS N t (K[/e]) = ρNS_ktx N t K e.
Proof.
unfold ρNS_ktx.
destruct (ev2v N t e) as [ [[[n t'] v] w] | ] eqn:H.
2:{ rewrite ev2v_None_then_ρNS_Ke_is_ρNT_e; auto. }
generalize N t K e n t' v w H; clear N t K e n t' v w H.
induction N; intros t K e n t' v w H.
1:{
  simpl Nat.sub. simpl in H.
  destruct (exp_val_dec e) as [ [u Hu] | Nonval_e ] eqn: He; inversion H; subst.
  ring.
}
simpl in H.
destruct (exp_val_dec e) as [ [u Hu] | Nonval_e ] eqn: He.
1:{
  subst. simpl in H. inversion H; subst.
  rewrite ennr_mul_1_l, <- minus_n_O. reflexivity.
}
destruct (sss_det (eval N) t e) as [ [t'' [e'' [w' [Step_e _]]]] | Stop_e ].
2:{ inversion H. }
destruct (ev2v N t'' e'') as [ [[[n_ t'_] v_] w_] | ] eqn:H'.
2:{ inversion H. }
inversion H; clear H. subst.
simpl minus.
apply ktx_congruence with (K := K) in Step_e as Step_Ke.
erewrite sss_preserves_ρNS; [ | exact Step_Ke ].
rewrite <- ennr_mul_assoc, ennr_mul_comm.
erewrite <- IHN; [ reflexivity | ].
apply H'.
Qed.

(* This lemma suggests entropy is correctly split between the redex and the
surrounding evaluation context *)
Lemma μNS_ktx_rewrite (N : nat) (K : ktx) (e : exp0) :
μNS N (K[/e]) =
∫ (λ t, match ev2v N t e with
  | Some (k, _, v, w) => w * μNS (N - k)%nat (K[/v])
  | None => 0
end) μentropy + μNT N e full_event.
Proof.
generalize K e; clear K e; induction N as [|N IHN]; intros K e.
1:{
  rewrite μNS_O.
  destruct (exp_val_dec e) as [[v Hv]|Nonval_e] eqn:dec_val_e.
  + subst. rewrite μNT_O_val. cbn.
    rewrite ennr_add_0_r. rewrite ennr_mul_1_l.
    erewrite integration_const_entropy; [reflexivity|].
    intro. unfold μNS_aux.
    erewrite integration_const_entropy; [reflexivity|].
    intro. unfold ρNS_aux. ring.
  + rewrite μNT_O_nonval; try assumption.
    match goal with | [ |- 1 = ?x + 1 ] => replace x with 0; [ring|] end.
    erewrite integration_const_entropy; [reflexivity|]. intro.
    simpl ev2v. rewrite dec_val_e. ring.
}
unfold μNT. rewrite integration_linear_plus.
(* setoid_rewrite ρNS_ktx_rewrite. *)
destruct (exp_val_dec e) as [ [v ?] | Nonval_e ] eqn:dec_val_e.
1:{
  subst.
  setoid_rewrite unfold_ev2v_val.
  rewrite <- minus_n_O. setoid_rewrite ennr_mul_1_l.
  setoid_rewrite ρNT_S_val. rewrite ennr_add_0_r.
  match goal with | [ |- _ = ∫ (λ _, ?x) _ ] =>
    erewrite integration_const_entropy with (f := (λ _, x));
    reflexivity
  end.
}
destruct (exp_ktx_exn_dec e) as [ [J ?] | Nonexn_e ].
1:{
  subst. rewrite ktx_plug_comp. rewrite <-μNS_exn.
  setoid_rewrite ev2v_ktx_exn. setoid_rewrite ennr_add_0_l.
  erewrite μNT_exn. reflexivity.
}
destruct (sss_exp_dec N e) as [ Step_e_N | Stop_e_N ].
2:{
  unfold μNS. setoid_rewrite ρNS_ktx_rewrite. unfold ρNS_ktx.
  integrand_extensionality t.
  rewrite ev2v_stuck.
  3:{ assumption. }
  2:{ split; assumption. }
  1:{ ring. }
}

specialize (Step_e_N entropy0) as [t' [e' [w Step_e_N]]].
destruct (sss_bifurcate Step_e_N) as [H | H].
+ erewrite sss_preserves_μNS.
  2:{ intro t. apply ktx_congruence. apply H. }
  rewrite IHN. unfold μNT. rewrite integration_linear_plus.
  rewrite <- integration_linear_mult_r. integrand_extensionality t.
  erewrite sss_ev2v with (e := e). 2:{ apply H. }
  erewrite sss_preserves_ρNT with (e := e). 2:{ apply H. }
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | [ |- context[(_ - _)%nat] ] => simpl Nat.sub 
  end; ring.
+ destruct H as [J [? [? [? ?]]]]. subst.
  rewrite ktx_plug_comp. erewrite ktx_sample_unif_preserves_μNS.
  setoid_rewrite <- ktx_plug_comp. setoid_rewrite IHN.
  rewrite <- integration_πU_lebesgue.
  unfold μNT. setoid_rewrite integration_linear_plus.
  rewrite <- integration_πL_πR.
  integrand_extensionality t.
  erewrite sss_ev2v.
  2:{ apply ktx_congruence. apply sss_sample_unif. }
  erewrite sss_preserves_ρNT.
  2:{ apply ktx_congruence. apply sss_sample_unif. }
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] => destruct x; simpl
  end; ring.
Qed.

Lemma μNS_le_1 N : ∀ e, μNS N e ≤ 1.
Proof.
induction N as [N IHN] using (well_founded_induction lt_wf).
intro e. destruct N as [ | N ].
1:{ rewrite μNS_O. apply ennr_le_refl. }
destruct (exp_val_dec e) as [ [v Hv] | Nonval_e ].
1:{ subst. rewrite μNS_val. apply ennr_le_refl. }
destruct (exp_ktx_exn_dec e) as [ [K ?] | Nonexn_e ].
1:{ subst. rewrite <-μNS_exn. apply ennr_le_refl. }
destruct (sss_exp_dec N e) as [ Step_e_N | Stop_e_N ].
2:{ rewrite <- μNS_stuck.
    - apply ennr_le_0.
    - split; assumption.
    - assumption. }
specialize (Step_e_N entropy0) as [t' [e' [w Step_e_N]]].
apply sss_quadfurcate in Step_e_N.
destruct Step_e_N as [ [Step_e_N Hw] | [ Step_e_N | [ Step_e_N | Step_e_N ]]].
+ erewrite sss_preserves_μNS; try apply Step_e_N.
  apply ennr_mult_le_1_compat; [|apply Hw].
  apply IHN. omega.
+ destruct Step_e_N as [K [f [? [? [? [? ?]]]]]]. subst.
  erewrite sss_preserves_μNS. 
  2:{ intro. apply ktx_congruence. apply sss_sample_query. assumption. }
  apply ennr_mult_inv_le_1_compat.
  rewrite μNS_ktx_rewrite.
  rewrite μNS_decompose with (e := f).
  apply ennr_add_le_compat_r.
  apply integrand_extensionality_le. intro t.
  rewrite <- ev2v_ρTV_same_weight.
  destruct (ev2v N t f) as [ [[[? ?] ?] ?] | ]; [cbn|apply ennr_le_0].
  rewrite <- ennr_mul_1_r. apply ennr_mult_le_compat_l.
  apply IHN. omega.
+ destruct Step_e_N as [K [f [? [? [? [? ?]]]]]]. subst.
  erewrite sss_preserves_μNS. 
  2:{ intro. apply ktx_congruence. apply sss_sample_query_exn; assumption. }
  rewrite ennr_mul_1_r. apply IHN. omega.
+ destruct Step_e_N as [K [? [? [? ?]]]]. subst.
  rewrite ktx_sample_unif_preserves_μNS.
  rewrite <- integration_πU_lebesgue.
  rewrite <- integration_const_entropy with (f := λ t, 1).
  2:{ intro. ring. }
  apply integrand_extensionality_le. intro t.
  apply IHN. omega.
Qed.

Lemma μNS_inf_le_1 e : μNS_inf e ≤ 1.
Proof.
eapply μNS_inf_le with (N := O). apply μNS_le_1.
Qed.

Lemma μNS_ktx_plug_le N K e : μNS N (K[/e]) ≤ μNS N e.
Proof.
generalize K e; clear K e. induction N as [|N IH]; intros K e.
1:{ repeat rewrite μNS_O. apply ennr_le_refl. }
destruct (exp_val_dec e) as [ [v Hv] | Nonval_e ].
1:{ subst. rewrite μNS_val. apply μNS_le_1. }
destruct (exp_ktx_exn_dec e) as [ [J ?] | Nonexn_e ].
1:{ subst. rewrite ktx_plug_comp. setoid_rewrite <-μNS_exn. apply ennr_le_refl. }
destruct (sss_exp_dec N e) as [ Step_e_N | Stop_e_N ].
2:{
  rewrite <- μNS_stuck with (e := K[/e]); try apply ennr_le_0.
  + split.
    - do 4 intro; intro Step_Ke_N.
      eapply sss_ktx_inv in Step_Ke_N as [? [? ?]]; try reflexivity; try eassumption.
      eapply Stop_e_N; eassumption.
    - intros J Q. apply ktx_plug_is_K_exn_inv in Q as [? [? ?]].
      2:{ apply Nonval_e. }
      subst. eapply Nonexn_e. reflexivity.
  + intros v H. apply ktx_plug_is_val_inv in H as [? ?]. subst.
    eapply Nonval_e. reflexivity.
}
specialize (Step_e_N entropy0) as [t' [e' [w Step_e_N]]].
apply sss_bifurcate in Step_e_N.
destruct Step_e_N as [ Step_e_N | Step_e_N ].
+ repeat erewrite sss_preserves_μNS; try apply Step_e_N.
  2:{ intro t. specialize (Step_e_N t). apply ktx_congruence. apply Step_e_N. }
  apply ennr_mult_le_compat_r. apply IH.
+ destruct Step_e_N as [J [? [? [? ?]]]]. subst.
  rewrite ktx_plug_comp. repeat rewrite ktx_sample_unif_preserves_μNS.
  apply integrand_extensionality_le. intro r.
  apply ennr_mult_le_compat_r. rewrite <- ktx_plug_comp. apply IH.
Qed.

Lemma μNS_inf_ktx_plug_le K e : μNS_inf (K[/e]) ≤ μNS_inf e.
Proof.
apply μNS_inf_is_glb. intro N.
eapply μNS_inf_le. apply μNS_ktx_plug_le.
Qed.

Lemma μNS_inf_ktx_stuck N e K :
stop N e →
(∀ v, e = exp_val v → False) →
0 = μNS_inf (K [/e]).
Proof.
intros Stop Notval_e.
apply ennr_le_0_is_0.
eapply ennr_le_trans.
apply μNS_inf_ktx_plug_le.
rewrite <- (μNS_inf_stuck Stop Notval_e).
auto.
Qed.

Lemma nat_eq_dec : ∀ n m : nat, {n = m} + {n ≠ m}.
Proof. decide equality. Defined.

Lemma μNS_ktx_rewrite_S (N : nat) (K : ktx) (e : exp0) :
μNS (S N) (K[/e]) =
∫ (λ t, match ev2v (S N) t e with
  | Some (k, _, v, w) => if lt_dec k (S N) then w * μNS (S N - k)%nat (K[/v]) else 0
  | None => 0
end) μentropy +
(∫ (λ t, match ev2v (S N) t e with
  | Some (k, _, _, w) => if nat_eq_dec k (S N) then w else 0
  | None => 0
end) μentropy +
μNT (S N) e full_event).
Proof.
rewrite μNS_ktx_rewrite. rewrite ennr_add_assoc. apply ennr_add_eq_compat_r.
rewrite integration_linear_plus.
integrand_extensionality t.
destruct (ev2v (S N) t e) as [[[[k ?] ?] ?] |] eqn:Ev2v. 2:{ ring. }
destruct (lt_eq_lt_dec k (S N)) as [[|]|], (lt_dec k (S N)), (nat_eq_dec k (S N)); subst; try omega; try ring.
{ simpl minus. rewrite <- minus_diag_reverse. rewrite μNS_O. ring. }
{ apply ev2v_index_bounded in Ev2v. omega. }
Qed.
