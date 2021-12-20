Require Import RRR.Lang.Lang.
Require Import RRR.Lebesgue.Lebesgue.
Require Import RRR.Rel.Relations.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Minus.
Require Import Coq.micromega.Lra.
Require Import FunctionalExtensionality.
Require ProofIrrelevance.
Require ssreflect.
Require ClassicalDescription.

Definition εNS n t K e := match ev2v n t e with
| Some (k, _, v, w) => w * μNS (n - k) (ktx_plug K v)
| None => 0
end.

Definition εNS' n t K e := match ev2v n t e with
| Some (k, _, v, w) => w * μNS n (ktx_plug K v)
| None => 0
end.

Fact εNS'_le_εNS n t K e : εNS' t n K e ≤ εNS t n K e.
Proof.
unfold εNS, εNS'.
repeat match goal with
| [ |- context[match ?x with _ => _ end] ] => destruct x
| [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
| [ |- ?x * ?y ≤ ?x ] => replace x with (x * 1) at 2 by apply ennr_mul_1_r
| [ |- ?x * ?y ≤ ?x * ?z ] => apply ennr_mult_le_compat_l
end. apply μNS_antitone. omega.
Qed.

Fact εNS_le_ρTV n t K e : εNS t n K e ≤ ρTV t n e full_event.
Proof.
unfold εNS. rewrite <-ev2v_ρTV_same_weight. unfold full_event, const.
repeat match goal with
| [ |- context[match ?x with _ => _ end] ] => destruct x
| [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
| [ |- ?x * ?y ≤ ?x ] => replace x with (x * 1) at 2 by apply ennr_mul_1_r
| [ |- ?x * ?y ≤ ?x * ?z ] => apply ennr_mult_le_compat_l
end. apply μNS_le_1.
Qed.

Fact εNS'_le_ρTV n t K e : εNS' t n K e ≤ ρTV t n e full_event.
Proof.
eapply ennr_le_trans. 1:{ apply εNS'_le_εNS. } apply εNS_le_ρTV.
Qed.

Definition νNS n K e := ∫ (λ t, εNS n t K e) μentropy.

Definition νNS' n K e := ∫ (λ t, εNS' n t K e) μentropy.

Fact νNS'_le_νNS n K e : νNS' n K e ≤ νNS n K e.
Proof.
intros. apply integrand_extensionality_le; intro t.
apply εNS'_le_εNS.
Qed.

Fact νNS_le_μTV n K e : νNS n K e ≤ μTV n e full_event.
Proof.
intros. apply integrand_extensionality_le; intro t.
apply εNS_le_ρTV.
Qed.

Fact νNS'_le_μTV n K e : νNS' n K e ≤ μTV n e full_event.
Proof.
intros. apply integrand_extensionality_le; intro t.
apply εNS'_le_ρTV.
Qed.

Fact μTV_minus_νNS_monotone_S n K e :
μTV n e full_event - νNS n K e ≤
μTV (S n) e full_event - νNS (S n) K e.
Proof.
  unfold μTV, νNS.
  repeat rewrite integration_linear_minus.
  3:{ intro. apply εNS_le_ρTV. }
  2:{ intro. apply εNS_le_ρTV. }
  setoid_rewrite <-ev2v_ρTV_same_weight. unfold full_event, const.
  unfold εNS.
  match goal with [ |- ?x ≤ _ ] => replace x with (
    ∫ (λ t, match ev2v n t e with
      | Some (k, _, v, w) =>
        (if ev2v (S n) t e then w else 0) *
        (1 - μNS (n - k) (ktx_plug K v))
      | None => 0
    end) μentropy +
    ∫ (λ t, match ev2v n t e with
      | Some (k, _, v, w) =>
        (if ev2v (S n) t e then 0 else w) *
        (1 - μNS (n - k) (ktx_plug K v))
      | None => 0
    end) μentropy
  ) end.
  2:{
    rewrite integration_linear_plus. integrand_extensionality t.
    repeat match goal with
    | [ |- context[match ?x with _ => _ end] ] => destruct x
    | [ |- ?x = ?x ] => ring
    | [ |- context[(0 * _)%ennr]] => rewrite ennr_mul_0_l
    | [ |- context[(0 + _)%ennr]] => rewrite ennr_add_0_l
    | [ |- context[(_ + 0)%ennr]] => rewrite ennr_add_0_r
    | [ |- context[(_ - 0)%ennr]] => rewrite ennr_minus_0
    | [ |- context[(_ * (_ - _))%ennr]] => rewrite ennr_minus_distr_r
    | [ |- context[(_ * 1)%ennr]] => rewrite ennr_mul_1_r
    | [ |- μNS _ _ ≤ 1 ] => apply μNS_le_1
    end.
  }
  match goal with [ |- _ + ?x ≤ _ ] => replace x with 0 end.
  2:{
    eapply ennr_mult_infinity_compat_0_eq.
    2:{ apply eq_sym. apply ev2v_monotone_S with (N := n) (e := e). }
    rewrite <- integration_linear_mult_l.
    apply integrand_extensionality_le. intro t.
    destruct (ev2v n t e) as [ [[[? ?] ?] ?] | ]. 2:{ apply ennr_le_0. }
    repeat match goal with
    | [ |- context[match ?x with _ => _ end] ] => destruct x
    | [ |- context[(0 * _)%ennr]] => rewrite ennr_mul_0_l
    | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
    | [ |- (_ ≤ ∞)%ennr ] => apply ennr_le_infinity
    | [ |- ?r * _ ≤ _ * ?r ] => rewrite ennr_mul_comm with (n := r)
    | [ |- _ * ?r ≤ _ * ?r ] => apply ennr_mult_le_compat_r
    end.
  }
  rewrite ennr_add_0_r.

  apply integrand_extensionality_le. intro t.
  destruct (ev2v n t e) as [[[[k0 t0] v0] w0]|] eqn:Ev2v_e_n,
      (ev2v (S n) t e) as [[[[k1 t1] v1] w1]|] eqn:Ev2v_e_Sn;
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
  | [ |- context[(_ - 0)%ennr] ] => rewrite ennr_minus_0
  | [ |- context[(_ * 1)%ennr] ] => rewrite ennr_mul_1_r
  | [ |- context[(0 * _)%ennr] ] => rewrite ennr_mul_0_l
  end.
  rewrite ennr_minus_distr_r. 2:{ apply μNS_le_1. }
  rewrite <- ennr_mul_1_r with (r := w1) at 1.
  repeat rewrite ennr_mul_comm with (n := w0).
  repeat rewrite ennr_mul_comm with (n := w1).
  repeat rewrite <- ennr_minus_distr_l; try apply μNS_le_1.
  eapply ev2v_S with (n := n) in Ev2v_e_Sn as [? [? [? ?]]]; try exact
  Ev2v_e_n. subst.
  apply ennr_mult_le_compat. 2:{ assumption. }
  apply ennr_minus_le_compat_r; try apply μNS_le_1.
  rewrite <- minus_Sn_m. 2:{ eapply ev2v_index_bounded; eassumption. }
  apply μNS_antitone_S.
Qed.

Fact μTV_minus_νNS_monotone K e :
monotone (λ n, μTV n e full_event - νNS n K e).
Proof.
do 2 intro. induction 1.
+ apply ennr_le_refl.
+ eapply ennr_le_trans; [eassumption|]. apply μTV_minus_νNS_monotone_S.
Qed.

Definition vt (T : ty) : Set := option { v : val0 | wf_val ∅→ v T }.

Definition ρTVT
(T : ty) (N : nat) (t : entropy) (e : exp0) (WF_e : wf_exp ∅→ e T)
(V : Event (vt T)) : R⁺.
Proof.
destruct (ev2v N t e) as [ [[[k t'] v] w] |] eqn:Ev2v.
2:{ refine 0. }
refine (
  if V (Some (exist _ v (ev2v_preserves_type Ev2v WF_e)))
  then w else 0
).
Defined.
Arguments ρTVT : clear implicits.

Definition μTVT
(T : ty) (N : nat) (e : exp0) (WF_e : wf_exp ∅→ e T) : Meas (vt T) :=
λ V, ∫ (λ t, ρTVT T N t e WF_e V) μentropy.
Arguments μTVT : clear implicits.

Definition μTVT_sup T e (WF_e : wf_exp ∅→ e T) V :=
sup (λ n, μTVT T n e WF_e V).
Arguments μTVT_sup T : clear implicits.

Definition μentropy_to_vt
(T : ty) (N : nat) (e : exp0) (WF_e : wf_exp ∅→ e T) :
entropy → vt T.
Proof.
intro t. destruct (ev2v N t e) as [ [[[k t'] v] w] |] eqn:Ev2v.
2:{ refine None. }
refine (Some (exist _ v _)).
apply (ev2v_preserves_type Ev2v WF_e).
Defined.
Arguments μentropy_to_vt : clear implicits.

Definition vkt (T : ty) : Set := option (nat * { v : val0 | wf_val ∅→ v T }).

Definition ρTVKT
(T : ty) (N : nat) (t : entropy) (e : exp0) (WF_e : wf_exp ∅→ e T)
(V : Event (vkt T)) : R⁺.
Proof.
destruct (ev2v N t e) as [ [[[k t'] v] w] |] eqn:Ev2v.
2:{ refine 0. }
refine (
  if V (Some (k, exist _ v (ev2v_preserves_type Ev2v WF_e)))
  then w else 0
).
Defined.
Arguments ρTVKT : clear implicits.

Definition μTVKT
(T : ty) (N : nat) (e : exp0) (WF_e : wf_exp ∅→ e T) : Meas (vkt T) :=
λ V, ∫ (λ t, ρTVKT T N t e WF_e V) μentropy.
Arguments μTVKT : clear implicits.

Definition μTVKT_sup T e (WF_e : wf_exp ∅→ e T) V :=
sup (λ n, μTVKT T n e WF_e V).
Arguments μTVKT_sup T : clear implicits.

Definition μentropy_to_vkt
(T : ty) (N : nat) (e : exp0) (WF_e : wf_exp ∅→ e T) :
entropy → vkt T.
Proof.
intro t. destruct (ev2v N t e) as [ [[[k t'] v] w] |] eqn:Ev2v.
2:{ refine None. }
refine (Some (k, exist _ v _)).
apply (ev2v_preserves_type Ev2v WF_e).
Defined.
Arguments μentropy_to_vkt : clear implicits.

Section section_μTVT_is_pushforward.
Import ssreflect.
Import ProofIrrelevance.
Import ClassicalDescription. (* for convenience *)

Lemma μTVT_is_μTV 
(T : ty) (N : nat) (e : exp0) (WF_e : wf_exp ∅→ e T)
(VT : Event (vt T)) :
μTVT T N e WF_e VT = μTV N e (λ v,
  match excluded_middle_informative (wf_val ∅→ v T) with
  | left WF_v => VT (Some (exist _ v WF_v))
  | right WF_v_false => false
  end
).
Proof.
unfold μTVT, μTV. integrand_extensionality t.
rewrite <-ev2v_ρTV_same_weight.
unfold ρTVT. generalize (eq_refl (ev2v N t e)).
case: {2 3}(ev2v N t e).
2:{ intro H. rewrite H. ring. }
intros [[[k t'] v] w]. intro H. rewrite H.
destruct (excluded_middle_informative _) as [WF_v|WF_v_false].
+ replace (ev2v_preserves_type H WF_e) with WF_v by apply proof_irrelevance.
  reflexivity.
+ exfalso. apply (WF_v_false (ev2v_preserves_type H WF_e)).
Qed.

Lemma μTVT_is_pushforward T N e (WF_e : wf_exp ∅→ e T) :
pushforward (score_meas (
  λ t, match ev2v N t e with
  | Some (_, _, _, w) => w
  | None => 0
  end
) μentropy) (μentropy_to_vt T N e WF_e) =
μTVT T N e WF_e.
Proof.
extensionality V. unfold pushforward, compose, μTVT.
unfold score_meas, ">>=".
integrand_extensionality t. unfold indicator, ifte, preimage.
unfold ρTVT. generalize (eq_refl (ev2v N t e)).
case: {2 3 4}(ev2v N t e). 2:{ intros. ring. }
intros [[[k t'] v] w]. intro H.
unfold μentropy_to_vt.
generalize (eq_refl (ev2v N t e)).
case: {2 3}(ev2v N t e).
2:{ intro H'. exfalso. rewrite H' in H. inversion H. }
intros [[[_k _t'] _v] _w]. intro H'.
assert (_k = k ∧ _v = v) as P.
2:{
  destruct P. subst _k _v.
  replace (ev2v_preserves_type H' WF_e) with
          (ev2v_preserves_type H WF_e)
          by apply proof_irrelevance.
  destruct (V _); ring.
}
rewrite H' in H. inversion H. subst. split; trivial.
Qed.

End section_μTVT_is_pushforward.

Section section_μTVKT_is_pushforward.
Import ssreflect.
Import ProofIrrelevance.

Lemma μTVKT_is_pushforward T N e (WF_e : wf_exp ∅→ e T) :
pushforward (score_meas (
  λ t, match ev2v N t e with
  | Some (_, _, _, w) => w
  | None => 0
  end
) μentropy) (μentropy_to_vkt T N e WF_e) =
μTVKT T N e WF_e.
Proof.
extensionality V. unfold pushforward, compose, μTVKT.
unfold score_meas, ">>=".
integrand_extensionality t. unfold indicator, ifte, preimage.
unfold ρTVKT. generalize (eq_refl (ev2v N t e)).
case: {2 3 4}(ev2v N t e). 2:{ intros. ring. }
intros [[[k t'] v] w]. intro H.
unfold μentropy_to_vkt. generalize (eq_refl (ev2v N t e)).
case: {2 3}(ev2v N t e).
2:{ intro H'. exfalso. rewrite H' in H. inversion H. }
intros [[[_k _t'] _v] _w]. intro H'.
assert (_k = k ∧ _v = v) as P.
2:{
  destruct P. subst _k _v.
  replace (ev2v_preserves_type H' WF_e) with
          (ev2v_preserves_type H WF_e)
          by apply proof_irrelevance.
  destruct (V _); ring.
}
rewrite H' in H. inversion H. subst. split; trivial.
Qed.

End section_μTVKT_is_pushforward.

Section section_μTV_minus_νNS_pushforward.
Import ProofIrrelevance.
Import ssreflect.

Fact μTV_minus_νNS'_pushforward_μTVT T n K e (WF_e : wf_exp ∅→ e T) :
μTV n e full_event - νNS' n K e =
∫ (λ v : vt T, 1 - 
  match v with
  | Some (exist _ v _) => μNS n (ktx_plug K v)
  | None => 0
  end
) (μTVT T n e WF_e).
Proof.
unfold μTV, νNS', εNS'. rewrite integration_linear_minus.
1:{ intro. apply εNS'_le_ρTV. }
rewrite <-μTVT_is_pushforward. rewrite <-integration_of_pushforward.
unfold compose. rewrite integration_wrt_score_meas.
integrand_extensionality t.
unfold μentropy_to_vt.
rewrite <-ev2v_ρTV_same_weight.
generalize (eq_refl (ev2v n t e)).
case: {2 3 4 5 12}(ev2v n t e).
2:{ intro H. repeat rewrite ennr_minus_0. ring. }
intros [[[k t'] v] w]. intro H.
unfold full_event, const.
rewrite ennr_minus_distr_l. 1:{ apply μNS_le_1. }
apply f_equal2; ring.
Qed.

Fact μTV_minus_νNS_pushforward_μTVKT T n K e (WF_e : wf_exp ∅→ e T) :
μTV n e full_event - νNS n K e =
∫ (λ v : vkt T, 1 - 
  match v with
  | Some (k, exist _ v _) => μNS (n - k) (ktx_plug K v)
  | None => 0
  end
) (μTVKT T n e WF_e).
Proof.
unfold μTV, νNS, εNS. rewrite integration_linear_minus.
1:{ intro. apply εNS_le_ρTV. }
rewrite <-μTVKT_is_pushforward. rewrite <-integration_of_pushforward.
unfold compose. rewrite integration_wrt_score_meas.
integrand_extensionality t.
unfold μentropy_to_vkt.
rewrite <-ev2v_ρTV_same_weight.
generalize (eq_refl (ev2v n t e)).
case: {2 3 4 5 12}(ev2v n t e).
2:{ intro H. repeat rewrite ennr_minus_0. ring. }
intros [[[k t'] v] w]. intro H.
unfold full_event, const.
rewrite ennr_minus_distr_l. 1:{ apply μNS_le_1. }
apply f_equal2; ring.
Qed.

Fact μTV_minus_νNS_pushforward_μTVT T n K e (WF_e : wf_exp ∅→ e T) :
μTV n e full_event - νNS n K e ≤
∫ (λ v : vt T, 1 - 
  match v with
  | Some (exist _ v _) => μNS n (ktx_plug K v)
  | None => 0
  end
) (μTVT T n e WF_e).
Proof.
rewrite <- μTV_minus_νNS'_pushforward_μTVT.
apply ennr_minus_le_compat_r.
3:{ apply νNS'_le_νNS. }
2:{ apply νNS'_le_μTV. }
1:{ apply νNS_le_μTV. }
Qed.

Lemma μTVKT_O_val T v V WF_v :
μTVKT T O (exp_val v) (wf_exp_val WF_v) V = if V (Some (O, exist _ v WF_v)) then 1 else 0.
Proof.
destruct (V _) eqn:Hv.
+ unfold μTVKT.
  replace 1 with (μentropy full_event).
  2:{ rewrite μentropy_is_a_probability_measure ; reflexivity. }
  rewrite <- integration_of_indicator. unfold indicator, ifte.
  integrand_extensionality t. cbn.
  replace (ev2v_preserves_type _ _) with WF_v by apply proof_irrelevance.
  rewrite Hv ; cbn ; ring.
+ unfold μTVKT. 
  erewrite <- integration_of_0.
  integrand_extensionality t. cbn.
  replace (ev2v_preserves_type _ _) with WF_v by apply proof_irrelevance.
  rewrite Hv ; cbn ; ring.
Qed.

Lemma μTVKT_S_val T N (v : val0) V WF_v :
μTVKT T (S N) v (wf_exp_val WF_v) V = μTVKT T N v (wf_exp_val WF_v) V.
Proof.
unfold μTVKT.
integrand_extensionality t.
unfold ρTVKT.
generalize (eq_refl (ev2v (S N) t v)).
case: {2 3}(ev2v (S N) t v).
2:{ intro H. exfalso. simpl in H. inversion H. }
generalize (eq_refl (ev2v N t v)).
case: {2 3}(ev2v N t v).
2:{ intro H. exfalso. rewrite unfold_ev2v_val in H. inversion H. }
intros [[[? ?] ?] ?] HN.
intros [[[? ?] ?] ?] HSN.
generalize (ev2v_preserves_type HN (wf_exp_val WF_v)).
generalize (ev2v_preserves_type HSN (wf_exp_val WF_v)).
intros WF_v' WF_v''.
rewrite unfold_ev2v_val in HN, HSN. inversion HN. inversion HSN. subst.
replace WF_v' with WF_v by apply proof_irrelevance.
replace WF_v'' with WF_v by apply proof_irrelevance.
reflexivity.
Qed.

Lemma μTVKT_val T N v V WF_v :
μTVKT T N (exp_val v) (wf_exp_val WF_v) V = if V (Some (O, exist _ v WF_v)) then 1 else 0.
Proof.
induction N.
+ apply μTVKT_O_val.
+ rewrite μTVKT_S_val ; apply IHN.
Qed.

Lemma ρTVKT_O_nonval T t e WF_e V :
(∀ v, e = exp_val v → False) → ρTVKT T O t e WF_e V = 0.
Proof.
intro H. unfold ρTVKT.
generalize (eq_refl (ev2v 0 t e)).
case: {2 3}(ev2v 0 t e). 2:{ reflexivity. }
intros [[[k t'] v] w] H0. exfalso.
simpl ev2v in H0. destruct (exp_val_dec e) as [[u ?]|].
2:{ inversion H0. }
inversion H0. subst. eapply H. reflexivity.
Qed.

Lemma μTVKT_O_nonval T e WF_e V :
(∀ v, e = exp_val v → False) → μTVKT T O e WF_e V = 0.
Proof.
intro H. unfold μTVKT.
erewrite <- integration_of_0.
integrand_extensionality t.
apply ρTVKT_O_nonval ; apply H.
Qed.

Lemma μTVKT_stuck_S T N e WF_e V :
stop N e →
(∀ v, e = exp_val v → False) →
0 = μTVKT T (S N) e WF_e V.
Proof.
intros Hstop e_not_val.
replace 0 with (0 * μentropy full_event) ; [ | ring ].
erewrite <- integration_of_const with (f := λ _, 0) ; [ | intro ; ring ].
integrand_extensionality t.
unfold ρTVKT.
generalize (eq_refl (ev2v (S N) t e)).
case: {2 3}(ev2v (S N) t e). 2:{ reflexivity. }
intros [[[k t'] v] w] Ev_e. exfalso.
simpl in Ev_e.
destruct (exp_val_dec e) as [ [u Hu] | ].
1:{ subst. eapply e_not_val. reflexivity. }
destruct Hstop as [Stuck_e NotExn_e].
destruct (exp_ktx_exn_dec e) as [ [K ?] | ].
1:{ subst. eapply NotExn_e. reflexivity. }
destruct (sss_det (eval N) t e) as [ [?[?[?[? ?]]]] |].
2:{ inversion Ev_e. }
specialize (Stuck_e t). eapply Stuck_e. eassumption.
Qed.

Definition S_VKT T (V : Event (vkt T)) : Event (vkt T).
Proof.
intro o. destruct o as [ [k [v Wf_v]] | ].
+ refine (V (Some (S k, exist _ v Wf_v))).
+ refine (V None).
Defined.

Lemma S_VKT_Some T (V : Event (vkt T)) k v WF_v :
V (Some (S k, exist _ v WF_v)) = S_VKT T V (Some (k, exist _ v WF_v)).
Proof.
unfold S_VKT. reflexivity.
Qed.

Lemma sss_preserves_ρTVKT T N t t' e e' WF_e w:
sss (eval N) t e t' e' w →
∀ (V V' : Event (vkt T)) WF_e',
(∀ k v WF_v, V (Some (S k, exist _ v WF_v)) = V' (Some (k, exist _ v WF_v))) →
ρTVKT T (S N) t e WF_e V = (ρTVKT T N t' e' WF_e' V') * w.
Proof.
intros Hsss V V' WF_e' HV.
apply sss_ev2v in Hsss.
unfold ρTVKT.
generalize dependent Hsss.
generalize (eq_refl (ev2v N t' e')).
case: {2 3 4}(ev2v N t' e').
2:{
  intros Ev_e'. generalize (eq_refl (ev2v (S N) t e)).
  case: {2 3 4}(ev2v (S N) t e). 2:{ intros. ring. }
  intros [[[? ?] ?] ?] ? Q. inversion Q.
}
intros [[[k t''] v] w'] Ev_e.
generalize (eq_refl (ev2v (S N) t e)).
case: {2 3 4}(ev2v (S N) t e). 2:{ intros ? Q. inversion Q. }
intros [[[_k _t''] _v] _w'] Ev_e'.
intro Q; inversion Q; clear Q; subst.
replace (ev2v_preserves_type Ev_e' WF_e) with
        (ev2v_preserves_type Ev_e WF_e') by apply proof_irrelevance.
rewrite <-HV.
destruct (V _); ring.
Qed.

Lemma sss_preserves_μTVKT T N e e' WF_e w:
(∀ t, sss (eval N) t e t e' w) →
∀ (V V' : Event (vkt T)) WF_e',
(∀ k v WF_v, V (Some (S k, exist _ v WF_v)) = V' (Some (k, exist _ v WF_v))) →
μTVKT T (S N) e WF_e V = unif_score_meas w (μTVKT T N e' WF_e') V'.
Proof.
intros Hsss V V' WF_e' HV.
unfold μTVKT.
simpl unif_score_meas.
rewrite <- integration_linear_mult_r.
integrand_extensionality t.
apply sss_preserves_ρTVKT. 2:{ apply HV. } apply Hsss.
Qed.

Lemma μTVKT_is_μTV_fullevent
(T : ty) (N : nat) (e : exp0) (WF_e : wf_exp ∅→ e T) :
μTVKT T N e WF_e full_event = μTV N e full_event.
Proof.
unfold μTVKT, μTV. integrand_extensionality t.
rewrite <-ev2v_ρTV_same_weight.
unfold ρTVKT. generalize (eq_refl (ev2v N t e)).
case: {2 3}(ev2v N t e).
2:{ intro H. rewrite H. ring. }
intros [[[k t'] v] w] H. rewrite H. simpl. ring.
Qed.

Lemma ρTVKT_monotone_in_V T (V' V : Event (vkt T)) :
(∀ v, if V' v then V v = true else True) →
∀ N t e WF_e, ρTVKT T N t e WF_e V' ≤ ρTVKT T N t e WF_e V.
Proof.
intros HV N t e WF_e. unfold ρTVKT.
generalize (eq_refl (ev2v N t e)).
case: {2 3 10}(ev2v N t e).
2:{ intros. apply ennr_le_0. }
intros [[[k t'] v] w] H.
specialize (HV (Some (k, exist _ v (ev2v_preserves_type H WF_e)))).
destruct (V' _).
+ rewrite HV. apply ennr_le_refl.
+ apply ennr_le_0.
Qed.

Lemma ρTVKT_le_full_event T N t e WF_e V :
ρTVKT T N t e WF_e V ≤ ρTVKT T N t e WF_e full_event.
Proof.
apply ρTVKT_monotone_in_V.
intro v. destruct (V v); reflexivity.
Qed.

Lemma μTVKT_le_full_event T N e WF_e V :
μTVKT T N e WF_e V ≤ μTVKT T N e WF_e full_event.
Proof.
apply integrand_extensionality_le.
intro; apply ρTVKT_le_full_event.
Qed.

Lemma μTVKT_le_μNS T N e WF_e V :
μTVKT T N e WF_e V ≤ μNS N e.
Proof.
eapply ennr_le_trans ; [ apply μTVKT_le_full_event |].
rewrite μNS_decompose. rewrite μTVKT_is_μTV_fullevent.
apply ennr_add_le_compat_1.
Qed.

Lemma ktx_sample_unif_preserves_μTVKT T N K WF_KSU :
∀ (V V' : Event (vkt T)),
(∀ k v WF_v, V (Some (S k, exist _ v WF_v)) = V' (Some (k, exist _ v WF_v))) →
∀ (WF_Kr : ∀ r, wf_exp ∅→ (ktx_plug K (val_real r)) T),
μTVKT T (S N) (ktx_plug K (exp_sample val_unif)) WF_KSU V =
∫ (λ r, μTVKT T N (ktx_plug K (val_real r)) (WF_Kr r) V' *
   match (Rinterval_dec 0 1 r) with
   | left _ => 1
   | right _ => 0
   end) lebesgue_measure.
Proof.
intros V V' HV WF_Kr.
unfold μTVKT.
rewrite <- integration_πU_lebesgue.
replace (λ t, ρTVKT T (S N) t (ktx_plug K (exp_sample val_unif)) WF_KSU V)
  with (λ t, ρTVKT T N (πR t) (ktx_plug K (val_real (πU t))) (WF_Kr (πU t)) V').
2:{
  extensionality t.
  erewrite sss_preserves_ρTVKT with (w := 1) (V' := V') (WF_e' := WF_Kr (πU t)).
  3:{ apply HV. }
  1:{ rewrite ennr_mul_1_r. reflexivity. }
  apply ktx_congruence.
  apply sss_sample_unif.
}
setoid_rewrite <- integration_πL_πR.
reflexivity.
Qed.

Lemma ρTVKT_exn T N t K WF_e V : 0 = ρTVKT T N t (ktx_plug K exp_exn) WF_e V.
Proof.
unfold ρTVKT.
generalize (eq_refl (ev2v N t (ktx_plug K exp_exn))).
case: {2 3}(ev2v N t (ktx_plug K exp_exn)).
2:{ reflexivity. }
intros [[[k t'] v] w] H.
exfalso. rewrite ev2v_ktx_exn in H. inversion H.
Qed.

Lemma μTVKT_exn T N K WF_e V : 0 = μTVKT T N (ktx_plug K exp_exn) WF_e V.
Proof.
unfold μTVKT. erewrite integration_const_entropy. 1:{ reflexivity. }
intro t. apply eq_sym. apply ρTVKT_exn.
Qed.

Section section_μTVKT_monotone_S.

Hint Constructors wf_exp wf_val : core.

Lemma μTVKT_monotone_S T : ∀ N e WF_e V,
μTVKT T N e WF_e V ≤ μTVKT T (S N) e WF_e V.
Proof.
induction N as [|N IH]; intros.
1:{
  destruct (exp_val_dec e) as [[v ?]|].
  + inversion WF_e; subst; try discriminate. inversion H0; subst.
    replace WF_e with (wf_exp_val H) by apply proof_irrelevance.
    repeat rewrite μTVKT_val. apply ennr_le_refl.
  + rewrite μTVKT_O_nonval. 1:{ assumption. } apply ennr_le_0.
}
destruct (exp_val_dec e) as [[v ?]|Notval_e].
1:{
  subst. inversion WF_e; subst.
  replace WF_e with (wf_exp_val H0) by apply proof_irrelevance.
  repeat rewrite μTVKT_val. apply ennr_le_refl.
}
destruct (exp_ktx_exn_dec e) as [[K ?]|Notexn_e].
1:{ subst. repeat rewrite <-μTVKT_exn. apply ennr_le_refl. }
destruct (sss_exp_dec N e) as [ Step_e_N | Stop_e_N ].
2:{
  rewrite <- μTVKT_stuck_S with (N := N). 1:{ apply ennr_le_0. }
  + split; assumption.
  + assumption.
}
specialize (Step_e_N entropy0) as [t' [e' [w Step_e_N]]].
apply sss_quadfurcate in Step_e_N.
destruct Step_e_N as [ [Step_e_N Hw] | [ Step_e_N | [ Step_e_N | Step_e_N ]] ].
+ eapply sss_preserves_type in WF_e as WF_e'.
  2:{ apply (Step_e_N O entropy0). }
  erewrite sss_preserves_μTVKT with (N := N) (V' := S_VKT T V) (WF_e' := WF_e').
  2:{ apply Step_e_N. } 2:{ reflexivity. }
  erewrite sss_preserves_μTVKT with (N := S N) (V' := S_VKT T V) (WF_e' := WF_e').
  2:{ apply Step_e_N. } 2:{ reflexivity. }
  cbn. apply ennr_mult_le_compat_r. apply IH.
+ destruct Step_e_N as [K [f [? [? [? [? ?]]]]]]. subst.
  assert (Step_Kf : ∀ t, sss (eval N) t (ktx_plug K (exp_sample (val_query f))) t (ktx_plug K f) (/ μNS N f)).
  1:{ intro. apply ktx_congruence. apply sss_sample_query. assumption. }
  specialize (Step_Kf entropy0) as WF_Kf.
  eapply sss_preserves_type in WF_Kf. 2:{ apply WF_e. }
  erewrite sss_preserves_μTVKT with (N := N) (V' := S_VKT T V) (WF_e' := WF_Kf). 
  2:{ apply Step_Kf. } 2:{ reflexivity. }
  destruct (ennr_0_lt_dec (μNS (S N) f)) as [NS_SN|NS_SN].
  1:{
    erewrite sss_preserves_μTVKT with (N := S N) (V' := S_VKT T V) (WF_e' := WF_Kf).
    2:{ intro. apply ktx_congruence. apply sss_sample_query. assumption. }
    2:{ reflexivity. }
    unfold unif_score_meas. apply ennr_mult_le_compat.
    + apply IH.
    + apply ennr_mult_inv_le_compat. apply μNS_antitone_S.
  }
  unfold unif_score_meas.
  replace (μTVKT T N (ktx_plug K f) _ _) with 0.
  1:{ rewrite ennr_mul_0_l. apply ennr_le_0. }
  apply ennr_le_0_is_0.
  rewrite NS_SN. eapply ennr_le_trans. 1:{ apply IH. }
  eapply ennr_le_trans. 1:{ apply μTVKT_le_μNS. }
  apply μNS_ktx_plug_le.
+ destruct Step_e_N as [K [f [? [NS_N [? [? ?]]]]]]. subst.
  assert (0 = μNS (S N) f) as NS_SN.
  1:{ apply ennr_le_0_is_0. rewrite NS_N. apply μNS_antitone_S. }
  assert (Step_Kf : ∀ t, sss (eval N) t (ktx_plug K (exp_sample (val_query f))) t (ktx_plug K exp_exn) 1).
  1:{ intro. apply ktx_congruence. apply sss_sample_query_exn. assumption. }
  specialize (Step_Kf entropy0) as WF_Kdiv.
  eapply sss_preserves_type in WF_Kdiv. 2:{ apply WF_e. }
  erewrite sss_preserves_μTVKT with (N := N) (V' := S_VKT T V) (WF_e' := WF_Kdiv). 
  3:{ reflexivity. } 2:{ apply Step_Kf. }
  erewrite sss_preserves_μTVKT with (N := S N) (V' := S_VKT T V) (WF_e' := WF_Kdiv).
  3:{ reflexivity. }
  2:{ intro t. apply ktx_congruence. apply sss_sample_query_exn. apply NS_SN. }
  cbn. repeat rewrite ennr_mul_1_r. apply IH.
+ destruct Step_e_N as [K [? [? [? ?]]]]. subst.
  assert (WF_Kr : ∀ r, wf_exp ∅→ (ktx_plug K (val_real r)) T).
  1:{
    clear- WF_e. generalize dependent T.
    induction K; simpl; intros; solve_pt; eauto.
  }
  erewrite ktx_sample_unif_preserves_μTVKT
    with (N := N) (V' := S_VKT T V) (WF_Kr := WF_Kr).
  2:{ reflexivity. }
  erewrite ktx_sample_unif_preserves_μTVKT
    with (N := S N) (V' := S_VKT T V) (WF_Kr := WF_Kr).
  2:{ reflexivity. }
  apply integrand_extensionality_le. intro t.
  apply ennr_mult_le_compat_r. apply IH.
Qed.

End section_μTVKT_monotone_S.

Lemma μTVKT_monotone T e A N' N WF_e :
N' <= N → μTVKT T N' e WF_e A ≤ μTVKT T N e WF_e A.
Proof.
induction 1 as [ | ? ? IH ] ; intros.
+ apply ennr_le_refl.
+ eapply ennr_le_trans; [ apply IH | ].
  apply μTVKT_monotone_S.
Qed.

Fact μTV_minus_νNS_pushforward_lim_μTVKT
T K e (WF_e : wf_exp ∅→ e T)
(HL : has_lim (λ n, μTV n e full_event - νNS n K e)) :
lim (λ n, μTV n e full_event - νNS n K e) HL =
∫ (λ v : vkt T, 1 - match v with
  | Some (_, exist _ v _) => μNS_inf (ktx_plug K v)
  | None => 0
end
) (μTVKT_sup T e WF_e).
Proof.
rewrite <-sup_is_lim' by apply μTV_minus_νNS_monotone.
specialize μTV_minus_νNS_pushforward_μTVKT with (WF_e := WF_e) as H.
setoid_rewrite H.
rewrite interchange_sup_integration_meas.
3:{
  integrand_extensionality v. destruct v as [[k [v WF_v]]|].
  2:{ apply sup_of_constant. intro; ring. }
  rewrite sup_of_constant_minus. apply f_equal2. 1:{ ring. }
  unfold μNS_inf. erewrite inf_antitone with (k := k).
  2:{ do 3 intro. apply μNS_antitone. omega. }
  apply f_equal. extensionality n.
  replace (n + k - k)%nat with n by omega. reflexivity.
}
2:{ intros. do 3 intro. apply μTVKT_monotone. omega. }
1:{
  intros [[k [v ?]]|].
  2:{ rewrite ennr_minus_0. do 3 intro. apply ennr_le_refl. }
  do 3 intro. apply ennr_minus_le_compat_r; try apply μNS_le_1.
  apply μNS_antitone. omega.
}
Qed.

Fact μTV_minus_νNS_pushforward_lim_μTVT
T K e (WF_e : wf_exp ∅→ e T)
(HL : has_lim (λ n, μTV n e full_event - νNS n K e)) :
lim (λ n, μTV n e full_event - νNS n K e) HL =
∫ (λ v : vt T, 1 - match v with
  | Some (exist _ v _) => μNS_inf (ktx_plug K v)
  | None => 0
end
) (μTVT_sup T e WF_e).
Proof.
specialize μTV_minus_νNS_pushforward_lim_μTVKT with (WF_e := WF_e) as H.
rewrite H. clear H.
apply integration_wrt_redundant_var. 1:{ ring. } 1:{ intros. ring. }
intro X. unfold μTVKT_sup, μTVT_sup. f_equal.
Qed.
End section_μTV_minus_νNS_pushforward.
