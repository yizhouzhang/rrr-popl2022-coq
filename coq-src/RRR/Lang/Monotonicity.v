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
Require Import RRR.Lang.Measure.
Require Import RRR.Lebesgue.Lebesgue.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Section section_sss_antitone_S_aux.
Context (n : nat).
Context (μNS_antitone : ∀ e, μNS (S n) e ≤ μNS n e).

Fact sss_antitone_S_aux_bifurcate e :
∀ t t' e' w₁, sss (eval (S n)) t e t' e' w₁ → (
  ∃ w₀, sss (eval n) t e t' e' w₀ ∧ w₀ ≤ w₁
) ∨ (
  ∃ K f, e = ktx_plug K (exp_sample (val_query f)) ∧
  t' = t ∧ e' = ktx_plug K exp_exn ∧
  w₁ = 1 ∧ 0 = μNS (S n) f ∧ 0 < μNS n f
).
Proof.
induction 1.
+ left. repeat eexists; [constructor|apply ennr_le_refl].
+ left. repeat eexists; [constructor|apply ennr_le_refl].
+ left. repeat eexists; [constructor|apply ennr_le_refl].
+ left. repeat eexists; [constructor; eauto|apply ennr_le_refl].
+ left. repeat eexists; [constructor|apply ennr_le_refl].
+ left. repeat eexists; [constructor|apply ennr_le_refl].
+ left. repeat eexists; [constructor|apply ennr_le_refl].
+ left. repeat eexists; [constructor|apply ennr_le_refl].
+ left. assert (0 < μNS n e) as NS.
  1:{ eapply ennr_lt_le_trans; [eassumption|apply μNS_antitone]. }
  repeat eexists.
  - apply sss_sample_query. apply NS.
  - apply ennr_mult_inv_le_compat. apply μNS_antitone.
+ destruct (ennr_0_lt_dec (μNS n e)) as [NS|NS].
  - right. eexists ktx_hole. repeat eexists; assumption.
  - left. repeat eexists.
    1:{ apply sss_sample_query_exn. apply NS. }
    apply ennr_le_refl.
+ left. repeat eexists; [unshelve constructor; auto|].
  apply ennr_le_refl.
+ destruct IHsss as [[w₀ [IHsss Hw]]|[K [f [? [? [? [? [? ?]]]]]]]].
  2:{ subst. right. eexists (ktx_app1 K _). repeat eexists; assumption. }
  left. repeat eexists. 2:{ apply Hw. }
  bind_ktx_app1. apply ktx_congruence; eassumption.
+ destruct IHsss as [[w₀ [IHsss Hw]]|[K [f [? [? [? [? [? ?]]]]]]]].
  2:{ subst. right. eexists (ktx_app2 _ K). repeat eexists; assumption. } left. repeat eexists. 2:{ apply Hw. }
  bind_ktx_app2. apply ktx_congruence; eassumption.
+ destruct IHsss as [[w₀ [IHsss Hw]]|[K [f [? [? [? [? [? ?]]]]]]]].
  2:{ subst. right. eexists (ktx_let K _). repeat eexists; assumption. }
  left. repeat eexists. 2:{ apply Hw. }
  bind_ktx_let. apply ktx_congruence; eassumption.
+ destruct IHsss as [[w₀ [IHsss Hw]]|[K [f [? [? [? [? [? ?]]]]]]]].
  2:{ subst. right. eexists (ktx_binop1 _ K _). repeat eexists; assumption. }
  left. repeat eexists. 2:{ apply Hw. }
  bind_ktx_binop1. apply ktx_congruence; eassumption.
+ destruct IHsss as [[w₀ [IHsss Hw]]|[K [f [? [? [? [? [? ?]]]]]]]].
  2:{ subst. right. eexists (ktx_binop2 _ _ K). repeat eexists; assumption. }
  left. repeat eexists. 2:{ apply Hw. }
  bind_ktx_binop2. apply ktx_congruence; eassumption.
+ destruct IHsss as [[w₀ [IHsss Hw]]|[K [f [? [? [? [? [? ?]]]]]]]].
  2:{ subst. right. eexists (ktx_proj K _). repeat eexists; assumption. }
  left. repeat eexists. 2:{ apply Hw. }
  bind_ktx_proj. apply ktx_congruence; eassumption.
+ destruct IHsss as [[w₀ [IHsss Hw]]|[K [f [? [? [? [? [? ?]]]]]]]].
  2:{ subst. right. eexists (ktx_if K _ _). repeat eexists; assumption. }
  left. repeat eexists. 2:{ apply Hw. }
  bind_ktx_if. apply ktx_congruence; eassumption.
+ destruct IHsss as [[w₀ [IHsss Hw]]|[K [f [? [? [? [? [? ?]]]]]]]].
  2:{ subst. right. eexists (ktx_sample K). repeat eexists; assumption. }
  left. repeat eexists. 2:{ apply Hw. }
  bind_ktx_sample. apply ktx_congruence; eassumption.
+ destruct IHsss as [[w₀ [IHsss Hw]]|[K [f [? [? [? [? [? ?]]]]]]]].
  2:{ subst. right. eexists (ktx_score K). repeat eexists; assumption. }
  left. repeat eexists. 2:{ apply Hw. }
  bind_ktx_score. apply ktx_congruence; eassumption.
Qed.

Fact sss_antitone_S_aux e :
∀ t t' e' w₁, sss (eval (S n)) t e t' e' w₁ →
∃ e₀ w₀, sss (eval n) t e t' e₀ w₀.
Proof.
do 4 intro. intro H.
apply sss_antitone_S_aux_bifurcate in H.
destruct H as [[? [? ?]] | [? [? [? [? [? [? [? ?]]]]]]]].
+ repeat eexists. eassumption.
+ subst. repeat eexists.
  apply ktx_congruence. apply sss_sample_query. assumption.
Qed.

Fact stop_monotone_S_aux e : stop n e → stop (S n) e.
Proof.
unfold stop. intros [Stop_n NotExn].
split.
+ do 4 intro. intro Step_Sn.
  apply sss_antitone_S_aux_bifurcate in Step_Sn as [ [? [Step_n ?]] | Step_Sn ].
  - eapply Stop_n. apply Step_n.
  - destruct Step_Sn as [K [f [? [? [? [? [? ?]]]]]]]. subst.
    eapply Stop_n with (t := t). apply ktx_congruence. apply sss_sample_query. assumption.
+ apply NotExn.
Qed.
End section_sss_antitone_S_aux.

Fixpoint
(** In general, [ev2v N t e = Some _ → ev2v (S N) t e = Some _] does not hold. *)
ev2v_monotone_S N e {struct N} :
∫ (λ t, match ev2v N t e with
  | Some (_, _, _, w) => if ev2v (S N) t e then 0 else w
  | None => 0
end) μentropy = 0
with
μNS_antitone_S n e {struct n} : μNS (S n) e ≤ μNS n e
with
μNS_antitone_S_minus_aux n e {struct n} :
∀ k, (k < n)%nat → μNS (S k) e ≤ μNS k e
with
ev2v_S n t e k0 t0 v0 w0 k1 t1 v1 w1
(Ev2v_e_n: ev2v n t e = Some (k0, t0, v0, w0))
(Ev2v_e_Sn: ev2v (S n) t e = Some (k1, t1, v1, w1)) {struct n} :
t0 = t1 ∧ k0 = k1 ∧ v0 = v1 ∧ w0 ≤ w1
with
μTV_monotone_S N e V {struct N} : μTV N e V ≤ μTV (S N) e V.
Proof.
{
clear- ev2v_S ev2v_monotone_S. 
destruct N as [ | N ].
1:{
  rewrite <- integration_const_entropy with (f := λ _, 0) by trivial.
  integrand_extensionality t.
  simpl ev2v. destruct (exp_val_dec e) as [[v Hv]|Nonval_e] eqn:Dec_val_e; ring.
}
destruct (sss_exp_dec N e) as [Step_e_N | Stop_e_N].
2:{
  rewrite <- integration_const_entropy with (f := λ _, 0) by trivial.
  integrand_extensionality t.
  destruct (exp_val_dec e) as [[v Hv]|Nonval_e].
  + subst. simpl. ring.
  + destruct (exp_ktx_exn_dec e) as [[K ?]|Nonexn_e].
    1:{ subst. rewrite ev2v_ktx_exn. ring. }
    rewrite ev2v_stuck.
    3:{ assumption. }
    2:{ split; assumption. }
    1:{ ring. }
}
specialize (Step_e_N entropy0) as [t' [e' [w Step_e_N]]].
apply sss_quadfurcate in Step_e_N.
destruct Step_e_N as [Step_e_N|[Step_e_N|[Step_e_N|Step_e_N]]].
+ destruct Step_e_N as [Step_e_N Hw].
  match goal with [ |- ∫ ?f _ = _ ] => replace f with (
    λ t, match ev2v N t e' with
      | Some (_, _, _, w') => if ev2v (S N) t e' then 0 else w * w'
      | None => 0
    end
  ) end.
  2:{
    extensionality t.
    specialize (Step_e_N (S N) t) as Step_e_SN.
    specialize (Step_e_N N t) as Step_e_N.
    apply sss_ev2v in Step_e_SN. apply sss_ev2v in Step_e_N.
    rewrite Step_e_SN, Step_e_N.
    destruct (ev2v N t e') as [ [[[? ?] ?] ?] | ],
             (ev2v (S N) t e') as [ [[[? ?] ?] ?] | ]; reflexivity.
  }
  apply eq_sym. eapply ennr_mult_infinity_compat_0_eq.
  2:{ apply eq_sym. apply ev2v_monotone_S with (e := e') (N := N). }
  rewrite <- integration_linear_mult_l.
  apply integrand_extensionality_le. intro t.
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
  | [ |- (_ ≤ ∞)%ennr ] => apply ennr_le_infinity
  | [ |- (_ * ?r ≤ _ * ?r)%ennr ] => apply ennr_mult_le_compat_r
  end.
+ destruct Step_e_N as [K [f [? [Pos_N [? [? ?]]]]]]. subst.
  destruct (ennr_0_lt_dec (μNS (S N) f)) as [Pos_SN|Zero_SN].
  - match goal with [ |- ∫ ?g _ = _ ] => replace g with (
      λ t, match ev2v N t (ktx_plug K f) with
        | Some (_, _, _, w') => if ev2v (S N) t (ktx_plug K f) then 0 else (/ μNS N f) * w'
        | None => 0
      end
    ) end.
    2:{
      extensionality t.
      erewrite sss_ev2v with (N := N) (e := ktx_plug K (exp_sample (val_query f))).
      2:{ apply ktx_congruence. apply sss_sample_query. assumption. }
      erewrite sss_ev2v with (N := S N) (e := ktx_plug K (exp_sample (val_query f))).
      2:{ apply ktx_congruence. apply sss_sample_query. assumption. }
      destruct (ev2v N t (ktx_plug K f)) as [ [[[? ?] ?] ?] | ],
      (ev2v (S N) t (ktx_plug K f)) as [ [[[? ?] ?] ?] | ]; reflexivity.
    }
    apply eq_sym. eapply ennr_mult_infinity_compat_0_eq.
    2:{ apply eq_sym. apply ev2v_monotone_S with (e := ktx_plug K f) (N := N). }
    rewrite <- integration_linear_mult_l.
    apply integrand_extensionality_le. intro t.
    repeat match goal with
    | [ |- context[match ?x with _ => _ end] ] => destruct x
    | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
    | [ |- (_ ≤ ∞)%ennr ] => apply ennr_le_infinity
    | [ |- (_ * ?r ≤ _ * ?r)%ennr ] => apply ennr_mult_le_compat_r
    end.
  - match goal with [ |- ∫ ?g _ = _ ] => replace g with (
      λ t, match ev2v N t (ktx_plug K f) with
        | Some (_, _, _, w') => if ev2v (S N) t (ktx_plug K f) then 0 else (/ μNS N f) * w'
        | None => 0
      end + match ev2v N t (ktx_plug K f) with
        | Some (_, _, _, w') => if ev2v (S N) t (ktx_plug K f) then (/ μNS N f) * w' else 0
        | None => 0
      end
    ) end.
    2:{
      extensionality t.
      erewrite sss_ev2v with (N := N) (e := ktx_plug K (exp_sample (val_query f))).
      2:{ apply ktx_congruence. apply sss_sample_query. assumption. }
      erewrite sss_ev2v with (e := ktx_plug K (exp_sample (val_query f))).

      2:{ apply ktx_congruence. apply sss_sample_query_exn. assumption. }
      rewrite ev2v_ktx_exn.
      destruct (ev2v N t (ktx_plug K f)) as [ [[[? ?] ?] ?] | ]. 2:{ ring. }
      destruct (ev2v (S N) t (ktx_plug K f)) as [ [[[? ?] ?] ?] | ]; ring.
    }
    rewrite <- integration_linear_plus.
    match goal with [ |- ?x + _ = 0 ] => replace x with 0 end.
    2:{
      eapply ennr_mult_infinity_compat_0_eq.
      2:{ apply eq_sym. apply ev2v_monotone_S with (e := ktx_plug K f) (N := N). }
      rewrite <- integration_linear_mult_l.
      apply integrand_extensionality_le. intro t.
      repeat match goal with
      | [ |- context[match ?x with _ => _ end] ] => destruct x
      | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
      | [ |- (_ ≤ ∞)%ennr ] => apply ennr_le_infinity
      | [ |- (_ * ?r ≤ _ * ?r)%ennr ] => apply ennr_mult_le_compat_r
      end.
    }
    match goal with [ |- 0 + ?x = 0 ] => replace x with 0 end; [ring|].
    assert (0 = μNS (S N) (ktx_plug K f)) as Zero_SN_K.
    1:{ apply ennr_le_0_is_0. rewrite Zero_SN. apply μNS_ktx_plug_le. }
    eapply ennr_mult_infinity_compat_0_eq. 2:{ apply Zero_SN_K. }
    unfold μNS at 2.
    rewrite <- integration_linear_mult_l.
    apply integrand_extensionality_le. intro t.
    destruct (ev2v N t (ktx_plug K f)) as [ [[[? ?] ?] ?] | ] eqn:HN. 2:{ apply ennr_le_0. }
    destruct (ev2v (S N) t (ktx_plug K f)) as [ [[[? ?] ?] ?] | ] eqn:HSN. 2:{ apply ennr_le_0. }
    unfold ρNS. erewrite ev2v_Some_eval. 2:{ apply HSN. }
    apply ennr_mult_le_compat.
    1:{ apply ennr_le_infinity. }
    (* apply mutual induction hypothesis *)
    eapply ev2v_S with (n := N) in HN. 2:{ apply HSN. } apply HN.
+ destruct Step_e_N as [K [f [? [NS [? [? ?]]]]]]. subst.
  rewrite integration_const_entropy with (v := 0). 1:{ ring. }
  intro t. erewrite sss_ev2v with (N := N).
  2:{ apply ktx_congruence. apply sss_sample_query_exn. assumption. }
  rewrite ev2v_ktx_exn. ring.
+ destruct Step_e_N as [K [? [? [? ?]]]]. subst.
  match goal with [ |- ∫ ?f _ = _ ] => replace f with (
    λ t, match ev2v N (πR t) (ktx_plug K (val_real (πU t))) with
      | Some (_, _, _, w) => if ev2v (S N) (πR t) (ktx_plug K (val_real (πU t))) then 0 else w
      | None => 0
    end
  ) end.
  2:{
    extensionality t.
    erewrite sss_ev2v with (N := N) (e := ktx_plug K (exp_sample val_unif)).
    2:{ apply ktx_congruence. apply sss_sample_unif. }
    erewrite sss_ev2v with (N := S N) (e := ktx_plug K (exp_sample val_unif)).
    2:{ apply ktx_congruence. apply sss_sample_unif. }
    destruct (ev2v N (πR t) (ktx_plug K (val_real (πU t)))) as [ [[[? ?] ?] ?] | ] eqn:P,
             (ev2v (S N) (πR t) (ktx_plug K (val_real (πU t)))) as [ [[[? ?] ?] ?] | ] eqn:Q; try reflexivity; try ring.
  }
  assert (0 = ∫ (λ (t1 : entropy), ∫ (λ t2,
    match ev2v N t2 (ktx_plug K (val_real (proj1_sig (t1 0%nat)))) with
    | Some (_, _, _, w) => if ev2v (S N) t2 (ktx_plug K (val_real (proj1_sig (t1 0%nat)))) then 0 else w
    | None => 0
    end
  ) μentropy) μentropy) as H.
  2:{ rewrite <- integration_πL_πR in H. auto. }
  assert (0 = ∫ (λ r, ∫ (λ t,
    match ev2v N t (ktx_plug K (val_real r)) with
    | Some (_, _, _, w) => if ev2v (S N) t (ktx_plug K (val_real r)) then 0 else w
    | None => 0
    end
  ) μentropy * (if Rinterval_dec 0 1 r then 1 else 0)) lebesgue_measure) as H.
  2:{ rewrite <- integration_πU_lebesgue in H. auto. }
  erewrite integration_of_const with (r := 0). 1:{ ring. }
  intro r. match goal with [ |- ?x * _ = 0 ] => replace x with 0 end. 1:{ ring. }
  eapply ennr_mult_infinity_compat_0_eq.
  2:{ apply eq_sym. apply ev2v_monotone_S with (e := ktx_plug K (val_real r)) (N := N). }
  rewrite <- integration_linear_mult_l.
  apply integrand_extensionality_le. intro t.
  repeat match goal with
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
  | [ |- (_ ≤ ∞)%ennr ] => apply ennr_le_infinity
  | [ |- (_ * ?r ≤ _ * ?r)%ennr ] => apply ennr_mult_le_compat_r
  end.
  repeat match goal with
  | [ H : ?P |- ?P ] => apply H
  | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
  | [ |- (_ ≤ ∞)%ennr ] => apply ennr_le_infinity
  | [ _ : 0 < ?r |- context[∞ * ?r] ] => rewrite ennr_mul_infinity_l
  | [ |- ?r ≤ ∞ * ?r ] => destruct (ennr_0_lt_dec e); subst
  end.
}
    
{
destruct n as [ | n ].
1:{ rewrite μNS_O. apply μNS_le_1. }
destruct (exp_val_dec e) as [ [v Hv] | NotVal_e ].
1:{ subst. repeat rewrite μNS_val. apply ennr_le_refl. }
destruct (exp_ktx_exn_dec e) as [ [K ?] | NotExn_e ].
1:{ subst. repeat rewrite <-μNS_exn. apply ennr_le_refl. }
destruct (sss_exp_dec n e) as [ Step_n | Stop_n ].
2:{
  rewrite <- μNS_stuck with (N := S n). 1:{ apply ennr_le_0. }
  * split.
    + intros t t' e' w Step_Sn.
      apply sss_antitone_S_aux in Step_Sn as [? [? Step_Sn]].
      2:{ apply μNS_antitone_S with (n := n). }
      eapply Stop_n. apply Step_Sn.
    + assumption.
  * assumption.
}
specialize Step_n as Step_n0.
specialize (Step_n0 entropy0) as [t' [e' [w Step_n0]]].
apply sss_quadfurcate in Step_n0.
destruct Step_n0 as [Q | [Q | [Q | Q]]].
+ clear t'. destruct Q as [Q ?].
  pose (Q (S n)) as Q_Sn. pose (Q n) as Q_n.
  assert (∀ K N t, sss (eval N) t (ktx_plug K e) t (ktx_plug K e') w) as QK.
  1:{ intros. apply ktx_congruence. eapply Q. }
  apply sss_preserves_μNS in Q_Sn. repeat rewrite Q_Sn.
  apply sss_preserves_μNS in Q_n. repeat rewrite Q_n.
  apply ennr_mult_le_compat_r. apply μNS_antitone_S with (n := n).
+ destruct Q as [K [f [? [NS_n [? [? ?]]]]]]. subst.
  assert (∀ K t,
  sss (eval n) t (ktx_plug K (exp_sample (val_query f)))
  t (ktx_plug K f) (/ μNS (n) f)
  ) as Step_Kf_n.
  1:{
  clear- NS_n. intros K t.
  apply ktx_congruence. constructor. assumption.
  }
  destruct (ennr_0_lt_dec (μNS (S n) f)) as [NS_Sn|NS_Sn].
  - assert (∀ K t,
      sss (eval (S n)) t (ktx_plug K (exp_sample (val_query f)))
      t (ktx_plug K f) (/ μNS (S n) f)
    ) as Step_Kf_Sn.
    1:{
      clear- NS_Sn. intros K t.
      apply ktx_congruence. constructor. assumption.
    }
    rename f into e.
    erewrite sss_preserves_μNS with (N := n); try apply Step_Kf_n.
    erewrite sss_preserves_μNS with (N := S n); try apply Step_Kf_Sn.
    replace (μNS (S n) e) with (μNS (S n) (ktx_plug ktx_hole e)) by trivial.
    replace (μNS n e) with (μNS n (ktx_plug ktx_hole e)) by trivial.
    repeat rewrite μNS_ktx_rewrite_S.
    repeat rewrite μNS_ktx_rewrite with (N := n).
    apply ennr_inv_useful_fact.
    5:{ rewrite <- μNS_ktx_rewrite. apply μNS_finite. }
    4:{ rewrite <- μNS_ktx_rewrite, <- μNS_ktx_rewrite_S. apply μNS_antitone_S with (n := n). }
    3:{
      simpl ktx_plug.
      repeat rewrite integration_linear_minus.
      2:{
        intro t. repeat match goal with
        | [ |- context[match ?x with _ => _ end] ] => destruct x
        | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
        | [ |- (?r * _ ≤ ?r * _)%ennr ] => apply ennr_mult_le_compat_l
        end. rewrite μNS_val. apply μNS_le_1.
      }
      2:{
        intro t. repeat match goal with
        | [ |- context[match ?x with _ => _ end] ] => destruct x
        | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
        | [ |- (?r * _ ≤ ?r * _)%ennr ] => apply ennr_mult_le_compat_l
        end. rewrite μNS_val. apply μNS_le_1.
      }

      match goal with [ |- ?x ≤ _ ] => replace x with (
        ∫ (λ t, match ev2v n t e with
          | Some (k, _, v, w) =>
            (if ev2v (S n) t e then w else 0) *
            (μNS (n - k) v - μNS (n - k) (ktx_plug K v))
          | None => 0
        end) μentropy +
        ∫ (λ t, match ev2v n t e with
          | Some (k, _, v, w) =>
            (if ev2v (S n) t e then 0 else w) *
            (μNS (n - k) v - μNS (n - k) (ktx_plug K v))
          | None => 0
        end) μentropy
      ) end.
      2:{
        rewrite integration_linear_plus. integrand_extensionality t.
        repeat match goal with
        | [ |- context[match ?x with _ => _ end] ] => destruct x
        | [ |- context[(0 * _)%ennr]] => rewrite ennr_mul_0_l
        | [ |- context[(0 + _)%ennr]] => rewrite ennr_add_0_l
        | [ |- context[(_ + 0)%ennr]] => rewrite ennr_add_0_r
        | [ |- context[(_ - 0)%ennr]] => rewrite ennr_minus_0
        end.
        3:{ ring. }
        2:{ apply ennr_minus_distr_r. apply μNS_ktx_plug_le. }
        1:{ apply ennr_minus_distr_r. apply μNS_ktx_plug_le. }
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
      | [ |- context[μNS _ (exp_val _)] ] => rewrite μNS_val
      end.
      2:{
        (* apply mutual induction hypothesis *)
        eapply ev2v_S with (n := n) in Ev2v_e_Sn as [? [? ?]]; try exact Ev2v_e_n.
        subst. assert ((n - k1 = 0)%nat) as P by omega. rewrite P.
        rewrite μNS_O, ennr_minus_self, ennr_mul_0_r. apply ennr_le_0.
      }
      rewrite ennr_minus_distr_r. 2:{ apply μNS_le_1. }
      rewrite <- ennr_mul_1_r with (r := w1) at 1.
      repeat rewrite ennr_mul_comm with (n := w0).
      repeat rewrite ennr_mul_comm with (n := w1).
      repeat rewrite <- ennr_minus_distr_l; try apply μNS_le_1.
      (* apply mutual induction hypothesis *)
      eapply ev2v_S with (n := n) in Ev2v_e_Sn as [? [? [? ?]]]; try exact
      Ev2v_e_n. subst.
      apply ennr_mult_le_compat. 2:{ assumption. }
      apply ennr_minus_le_compat_r; try apply μNS_le_1.
      rewrite <- minus_Sn_m. 2:{ omega. }
      destruct k1.
      - rewrite <- minus_n_O. apply μNS_antitone_S with (n := n).
      - (* apply mutual induction hypothesis *)
        apply μNS_antitone_S_minus_aux with (n := n). omega.
    }
    2:{
      simpl ktx_plug. apply integrand_extensionality_le; intro t.
      repeat match goal with
      | [ |- context[match ?x with _ => _ end] ] => destruct x
      | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
      end. apply ennr_mult_le_compat_l. rewrite μNS_val. apply μNS_le_1.
    }
    1:{
      simpl ktx_plug. apply integrand_extensionality_le; intro t.
      repeat match goal with
      | [ |- context[match ?x with _ => _ end] ] => destruct x
      | [ |- (0 ≤ _)%ennr ] => apply ennr_le_0
      end. apply ennr_mult_le_compat_l. rewrite μNS_val. apply μNS_le_1.
    }
  - erewrite sss_preserves_μNS with (N := n).
    2:{ intro. apply ktx_congruence. apply sss_sample_query. apply NS_n. }
    assert (0 = μTV n f full_event) as TV_n.
    1:{
      apply ennr_le_0_is_0. rewrite NS_Sn.
      eapply ennr_le_trans. 2:{ apply μTV_le_μNS. }
      apply μTV_monotone_S with (N := n). (* apply mutual induction hypothesis *)
    }
    replace (μNS n (ktx_plug K f)) with (μNS n f).
    1:{
      rewrite ennr_mult_inv_r_finite.
      + apply μNS_le_1.
      + apply NS_n.
      + apply μNS_finite.
    }
    rewrite μNS_decompose with (e := f). rewrite <- TV_n, ennr_add_0_l.
    rewrite μNS_ktx_rewrite. match goal with
      [ |- ?x = ?y + ?x ] => replace y with 0
    end. 1:{ ring. }
    apply ennr_mult_infinity_compat_0_eq with (r2 := μTV n f full_event).
    2:{ apply TV_n. }
    unfold μTV. rewrite <- integration_linear_mult_l.
    apply integrand_extensionality_le. intro t.
    rewrite <- ev2v_ρTV_same_weight. destruct (ev2v n t f) as [[[[? ?] ?] ?]|].
    2:{ apply ennr_le_0. }
    1:{ rewrite ennr_mul_comm. apply ennr_mult_le_compat_r. apply ennr_le_infinity. }
+ destruct Q as [K [f [? [NS_n [? [? ?]]]]]]. subst.
  assert (0 = μNS (S n) f) as NS_Sn.
  1:{ apply ennr_le_0_is_0. rewrite NS_n. apply μNS_antitone_S with (n := n). }
  erewrite sss_preserves_μNS with (N := n).
  2:{ intro t. apply ktx_congruence. apply sss_sample_query_exn. apply NS_n. }
  erewrite sss_preserves_μNS with (N := S n).
  2:{ intro t. apply ktx_congruence. apply sss_sample_query_exn. apply NS_Sn. }
  repeat erewrite <-μNS_exn. rewrite ennr_mul_1_r. apply ennr_le_refl.
+ destruct Q as [K [? [? [? ?]]]]. subst.
  repeat rewrite ktx_sample_unif_preserves_μNS.
  apply integrand_extensionality_le. intro r.
  apply ennr_mult_le_compat_r.
  apply μNS_antitone_S with (n := n).
}

{
destruct n as [|n].
1:{ intros. exfalso. omega. }
induction k as [|k IHk].
1:{ intro. rewrite μNS_O. apply μNS_le_1. }
intro H.
destruct (lt_eq_lt_dec k (n - 1)) as [ [|] | ].
+ (* apply mutual induction hypothesis *)
  apply μNS_antitone_S_minus_aux with (n := n). omega.
+ assert (S k = n) as Q. 1:{ omega. } rewrite Q.
  (* apply mutual induction hypothesis *)
  apply μNS_antitone_S with (n := n).
+ exfalso. omega.
}

{
destruct n as [|n].
1:{
  cbn in *.
  destruct (exp_val_dec e) as [[v Hv] | Nonval_e ].
  + inversion Ev2v_e_n. inversion Ev2v_e_Sn. subst.
    repeat split. apply ennr_le_refl.
  + inversion Ev2v_e_n.
}
apply unfold_ev2v_S_to_Some in Ev2v_e_n.
apply unfold_ev2v_S_to_Some in Ev2v_e_Sn.
destruct Ev2v_e_n as [Ev2v_e_n|Ev2v_e_n], Ev2v_e_Sn as [Ev2v_e_Sn|Ev2v_e_Sn].
+ destruct Ev2v_e_n as [? [? [? ?]]], Ev2v_e_Sn as [? [? [? ?]]]. subst.
  match goal with [H : exp_val _ = exp_val _ |- _] => inversion H; clear H end. subst.
  repeat split. apply ennr_le_refl.
+ destruct Ev2v_e_n as [? [? [? ?]]], Ev2v_e_Sn as [? [? [? [? [? [? [? [?
?]]]]]]]].
  subst. match goal with [H : sss _ ?t (exp_val _) _ _ _ |- _ ] => inversion H end.
+ destruct Ev2v_e_Sn as [? [? [? ?]]], Ev2v_e_n as [? [? [? [? [? [? [? [?
?]]]]]]]].
  subst. match goal with [H : sss _ ?t (exp_val _) _ _ _ |- _ ] => inversion H end.
+ destruct Ev2v_e_n as [? [? [? [? [Step_n [? [? [? Ev2v_n]]]]]]]], Ev2v_e_Sn as [? [t' [e' [? [Step_Sn [? [? [? Ev2v_Sn]]]]]]]].
  subst.
  apply sss_quadfurcate in Step_n as Q. destruct Q as [Q | [Q | [Q | Q]]].
  - destruct Q as [Q Hw].
    specialize (Q (S n) t) as Step_Sn'.
    specialize (Q n t) as Step_n'.
    destruct (sss_unique Step_Sn' Step_Sn) as [? [? ?]]. subst.
    destruct (sss_unique Step_n Step_n') as [? [? ?]]. subst.
    eapply ev2v_S with (n := n) in Ev2v_Sn as [? [? [? ?]]]; try exact Ev2v_n. subst.
    repeat split. apply ennr_mult_le_compat_l. assumption.
  - destruct Q as [K [f [? [? [? [? ?]]]]]]. subst.
    eapply sss_ktx_inv in Step_n; try reflexivity.
    2:{ inversion 1. }
    eapply sss_ktx_inv in Step_Sn; try reflexivity.
    2:{ inversion 1. }
    destruct Step_n as [? [Step_n ?]]. inversion Step_n; subst.
    3:{ subst. match goal with [H : sss _ ?t (exp_val _) _ _ _ |- _ ] => inversion H end. }
    2:{ match goal with [H1: 0 = ?x, H2: 1 = / ?x |- _ ] => rewrite <-H1 in H2; rewrite ennr_inv_0 in H2; inversion H2 end. }
    destruct Step_Sn as [? [Step_Sn ?]]. inversion Step_Sn; subst.
    3:{ subst. match goal with [H : sss _ ?t (exp_val _) _ _ _ |- _ ] => inversion H end. }
    2:{ rewrite ev2v_ktx_exn in Ev2v_Sn. inversion Ev2v_Sn. }
    eapply ev2v_S with (n := n) in Ev2v_Sn as [? [? [? ?]]]; try exact Ev2v_n. subst.
    repeat split. apply ennr_mult_le_compat; try assumption.
    apply ennr_mult_inv_le_compat.
    apply μNS_antitone_S with (n := n). (* apply mutual induction hypothesis *)
  - destruct Q as [K [? [? [? [? [? ?]]]]]]. subst.
    rewrite ev2v_ktx_exn in Ev2v_n. inversion Ev2v_n.
  - destruct Q as [K [? [? [? ?]]]]. subst.
    eapply sss_ktx_inv in Step_Sn; try reflexivity.
    2:{ inversion 1. }
    destruct Step_Sn as [? [Step_Sn ?]]. inversion Step_Sn; subst.
    2:{ subst. match goal with [H : sss _ ?t (exp_val _) _ _ _ |- _ ] => inversion H end. }
    eapply ev2v_S with (n := n) in Ev2v_Sn as [? [? [? ?]]]; try apply Ev2v_n. subst.
    repeat rewrite ennr_mul_1_l. repeat split. assumption.
}
{
destruct N as [|N].
1:{
  destruct (exp_val_dec e) as [[v ?]|].
  + subst. repeat rewrite μTV_val. apply ennr_le_refl.
  + rewrite μTV_O_nonval by assumption. apply ennr_le_0.
}
destruct (exp_val_dec e) as [[v ?]|Notval_e].
1:{ subst. repeat rewrite μTV_val. apply ennr_le_refl. }
destruct (exp_ktx_exn_dec e) as [[K ?]|Notexn_e].
1:{ subst. repeat rewrite <-μTV_exn. apply ennr_le_refl. }
destruct (sss_exp_dec N e) as [ Step_e_N | Stop_e_N ].
2:{
  rewrite <- μTV_stuck_S with (N := N). 1:{apply ennr_le_0. }
  + split; assumption.
  + assumption.
}
specialize (Step_e_N entropy0) as [t' [e' [w Step_e_N]]].
apply sss_quadfurcate in Step_e_N.
destruct Step_e_N as [ [Step_e_N Hw] | [ Step_e_N | [ Step_e_N | Step_e_N ]] ].
+ erewrite sss_preserves_μTV with (N := N) by apply Step_e_N.
  erewrite sss_preserves_μTV with (N := S N) by apply Step_e_N.
  cbn. apply ennr_mult_le_compat_r. apply μTV_monotone_S with (N := N).
+ destruct Step_e_N as [K [f [? [? [? [? ?]]]]]]. subst.
  erewrite sss_preserves_μTV with (N := N). 
  2:{ intro. apply ktx_congruence. apply sss_sample_query. assumption. }
  destruct (ennr_0_lt_dec (μNS (S N) f)) as [NS_SN|NS_SN].
  1:{
    erewrite sss_preserves_μTV with (N := S N). 
    2:{ intro. apply ktx_congruence. apply sss_sample_query. assumption. }
    unfold unif_score_meas. apply ennr_mult_le_compat.
    + apply μTV_monotone_S with (N := N).
    + apply ennr_mult_inv_le_compat.
      apply μNS_antitone_S with (n := N). (* apply mutual induction hypothesis *)
  }
  unfold unif_score_meas.
  replace (μTV N (ktx_plug K f) V) with 0.
  1:{ rewrite ennr_mul_0_l. apply ennr_le_0. }
  apply ennr_le_0_is_0.
  rewrite NS_SN. eapply ennr_le_trans. 1:{ apply μTV_monotone_S with (N := N). }
  eapply ennr_le_trans. 1:{ apply μTV_le_μNS. }
  apply μNS_ktx_plug_le.
+ destruct Step_e_N as [K [f [? [NS_N [? [? ?]]]]]]. subst.
  assert (0 = μNS (S N) f) as NS_SN.
  1:{ apply ennr_le_0_is_0. rewrite NS_N.
      apply μNS_antitone_S with (n := N). (* apply mutual induction hypothesis *) }
  erewrite sss_preserves_μTV with (N := N).
  2:{ intro t. apply ktx_congruence. apply sss_sample_query_exn. apply NS_N. }
  erewrite sss_preserves_μTV with (N := S N).
  2:{ intro t. apply ktx_congruence. apply sss_sample_query_exn. apply NS_SN. }
  cbn. repeat rewrite ennr_mul_1_r. apply μTV_monotone_S with (N := N).
+ destruct Step_e_N as [K [? [? [? ?]]]]. subst.
  rewrite ktx_sample_unif_preserves_μTV with (N := N).
  rewrite ktx_sample_unif_preserves_μTV with (N := S N).
  apply integrand_extensionality_le. intro t.
  apply ennr_mult_le_compat_r. apply μTV_monotone_S with (N := N).
}
Qed.

Lemma μTV_monotone e A N' N :
N' <= N → μTV N' e A ≤ μTV N e A.
Proof.
induction 1 as [ | ? ? IH ] ; intros.
+ apply ennr_le_refl.
+ eapply ennr_le_trans; [ apply IH | ].
  apply μTV_monotone_S.
Qed.

Lemma μNS_antitone e N' N :
N' <= N → μNS N e ≤ μNS N' e.
Proof.
induction 1 as [ | ? ? IH ] ; intros.
+ apply ennr_le_refl.
+ eapply ennr_le_trans ; [ | apply IH ].
  apply μNS_antitone_S.
Qed.

Lemma μNT_antitone e : antitone (λ n, μNT n e full_event).
Proof.
unfold antitone. intros N' N HN.
repeat rewrite μNT_as_diff.
apply ennr_minus_le_compat.
4:{ apply μNS_antitone. omega. }
3:{ apply μTV_monotone. omega. }
2:{ apply μTV_le_μNS. }
1:{ apply μTV_le_μNS. }
Qed.

Lemma sss_preserves_μTV_sup e e' w:
(∀ N t, sss (eval N) t e t e' w) →
∀ V, μTV_sup e V = unif_score_meas w (μTV_sup e') V.
Proof.
intros Hsss V. simpl unif_score_meas. unfold μTV_sup.
rewrite <- sup_linear_mult_r.
2:{
  intro H. exfalso. specialize (Hsss O entropy0).
  apply sss_weight_finite in Hsss. rewrite H in Hsss. 
  apply ennr_lt_irrefl in Hsss. auto.
}
rewrite sup_S. 2:{ apply μTV_monotone_S. }
apply sup_extensionality. intro n.
erewrite sss_preserves_μTV by eapply Hsss.
reflexivity.
Qed.

Lemma sss_preserves_μNS_inf e e' w:
(∀ N t, sss (eval N) t e t e' w) →
μNS_inf e = μNS_inf e' * w.
Proof.
intros Hsss. unfold μNS_inf.
rewrite <- inf_linear_mult_r.
2:{
  intro.
  pose (inf_is_glb (λ N, μNS N e')) as Q.
  destruct Q as [Q _]. unfold is_lower_bound in Q.
  eapply ennr_le_lt_trans.
  1:{ apply Q. exists O. rewrite μNS_O. reflexivity. }
  simpl. trivial.
}
rewrite inf_S. 2:{ apply μNS_antitone_S. }
apply inf_extensionality. intro n.
erewrite sss_preserves_μNS by eapply Hsss.
reflexivity.
Qed.

Lemma ktx_sample_unif_preserves_μTV_sup K V :
μTV_sup (ktx_plug K (exp_sample val_unif)) V =
∫ (λ r, μTV_sup (ktx_plug K (val_real r)) V * if (Rinterval_dec 0 1 r) then 1 else 0) lebesgue_measure.
Proof.
unfold μTV_sup.
rewrite sup_S by apply μTV_monotone_S.
setoid_rewrite ktx_sample_unif_preserves_μTV.
rewrite interchange_sup_integration.
2:{
  intro r. intros n n' Nle.
  apply ennr_mult_le_compat_r. apply μTV_monotone. omega.
}
integrand_extensionality r.
rewrite sup_linear_mult_r.
2:{ intro H. exfalso. destruct (Rinterval_dec 0 1 r); inversion H. }
reflexivity.
Qed.

Lemma ktx_sample_unif_preserves_μNS_inf K :
μNS_inf (ktx_plug K (exp_sample val_unif)) =
∫ (λ r, μNS_inf (ktx_plug K (val_real r)) * if (Rinterval_dec 0 1 r) then 1 else 0) lebesgue_measure.
Proof.
unfold μNS_inf.
rewrite inf_S by apply μNS_antitone_S.
setoid_rewrite ktx_sample_unif_preserves_μNS.
rewrite interchange_inf_integration.
2:{
  intro r. intros n n' Nle.
  apply ennr_mult_le_compat_r. apply μNS_antitone. omega.
}
integrand_extensionality r.
rewrite inf_linear_mult_r.
2:{
  intro H. eapply ennr_le_lt_trans; [apply μNS_inf_le_1|]. simpl. trivial.
}
reflexivity.
Qed.

Lemma μTV_has_lim e V : has_lim (λ n, μTV n e V).
Proof.
apply monotone_has_lim. unfold monotone. apply μTV_monotone.
Qed.

Lemma μNS_has_lim e : has_lim (λ n, μNS n e).
Proof.
apply antitone_has_lim. unfold antitone. apply μNS_antitone.
Qed.

Lemma μNT_has_lim e : has_lim (λ n, μNT n e full_event).
Proof.
apply antitone_has_lim. unfold antitone. apply μNT_antitone.
Qed.

Ltac generalize_has_lim := repeat let HL := fresh "HasLim" in
match goal with
| [ |- context[monotone_has_lim ?f ?H] ] =>
  generalize (monotone_has_lim f H) as HL; intro HL
| [ |- context[antitone_has_lim ?f ?H] ] =>
  generalize (antitone_has_lim f H) as HL; intro HL
| [ |- context[prod_has_lim ?f ?g ?Hf ?Hg] ] =>
  generalize (prod_has_lim f g Hf Hg) as HL; intro HL
| [ |- context[inv_has_lim ?f ?H] ] =>
  generalize (inv_has_lim f H) as HL; intro HL
| [ |- context[μNS_has_lim ?e] ] =>
  generalize (μNS_has_lim e) as HL; intro HL
| [ |- context[μTV_has_lim ?e ?V] ] =>
  generalize (μTV_has_lim e V) as HL; intro HL
| [ |- context[μNT_has_lim ?e] ] =>
  generalize (μNT_has_lim e) as HL; intro HL
end.

Lemma ktx_sample_query_preserves_μTV_sup e :
0 < μNS_inf e →
∀ K V,
μTV_sup (ktx_plug K (exp_sample (val_query e))) V =
μTV_sup (ktx_plug K e) V * / μNS_inf e.
Proof.
intro NS_e. intro K. intro V.
unfold μTV_sup, μNS_inf.
rewrite sup_S. 2:{ apply μTV_monotone_S. }
unshelve erewrite sup_is_lim with (f := λ n, μTV (S n) _ _).
1:{ unfold monotone. intros. apply μTV_monotone. omega. }
generalize_has_lim.
unshelve erewrite sup_is_lim with (f := λ n, μTV n (ktx_plug K e) V).
1:{ unfold monotone. apply μTV_monotone. }
generalize_has_lim.
unshelve erewrite inf_is_lim with (f := λ n, μNS n e).
1:{ unfold antitone. apply μNS_antitone. }
generalize_has_lim.
unshelve erewrite <-lim_of_inv.
generalize_has_lim.
unshelve erewrite <-lim_of_product.
1:{
  apply prod_has_lim.
  + apply μTV_has_lim.
  + apply inv_has_lim. apply μNS_has_lim.
}
3:{
  intro H. exfalso. unshelve erewrite lim_of_inv' in H.
  1:{ apply μNS_has_lim. }
  apply ennr_inv_is_zero in H.
  rewrite <-inf_is_lim' in H. 2:{ unfold antitone. apply μNS_antitone. }
  specialize (μNS_inf_le_1 e) as H'. unfold μNS_inf in H'.
  rewrite H in H'. repeat match goal with
  | [ H: ∞ ≤ 1 |- _ ] => inversion H; clear H
  | [ H: ∞ < 1 |- _ ] => inversion H; clear H
  | [ H: ∞ = 1 |- _ ] => inversion H; clear H
  end.
}
2:{
  intro. unshelve erewrite lim_of_inv'. 
  1:{ apply μNS_has_lim. }
  apply ennr_inv_lt_infinity.
  rewrite <-inf_is_lim'. 2:{ unfold antitone. apply μNS_antitone. }
  apply NS_e.
}
generalize_has_lim.
apply lim_extensionality. intro n. assert (0 < μNS n e).
1:{
  unfold μNS_inf in NS_e.
  specialize (inf_is_glb (λ n, μNS n e)) as Q. destruct Q as [Q _].
  unfold is_lower_bound in Q. eapply ennr_lt_le_trans; [apply NS_e|].
  apply Q. repeat eexists.
}
erewrite sss_preserves_μTV.
2:{ intro. apply ktx_congruence. apply sss_sample_query. assumption. }
cbn. reflexivity.
Qed.

Lemma ktx_sample_query_preserves_μNS_inf e :
0 < μNS_inf e →
∀ K,
μNS_inf (ktx_plug K (exp_sample (val_query e))) =
μNS_inf (ktx_plug K e) * / μNS_inf e.
Proof.
intro NS_e. intro K.
unfold μNS_inf.
rewrite inf_S. 2:{ apply μNS_antitone_S. }
unshelve erewrite inf_is_lim with (f := λ n, μNS (S n) _).
1:{ unfold antitone. intros. apply μNS_antitone. omega. }
generalize_has_lim.
unshelve erewrite inf_is_lim with (f := λ n, μNS n (ktx_plug K e)).
1:{ unfold antitone. apply μNS_antitone. }
generalize_has_lim.
unshelve erewrite inf_is_lim with (f := λ n, μNS n e).
1:{ unfold antitone. apply μNS_antitone. }
generalize_has_lim.
rewrite <-lim_of_inv.
unshelve erewrite <-lim_of_product.
1:{
  apply prod_has_lim.
  + apply μNS_has_lim.
  + apply inv_has_lim. apply μNS_has_lim.
}
3:{
  intro H. exfalso. rewrite lim_of_inv in H. apply ennr_inv_is_zero in H.
  rewrite <-inf_is_lim' in H. 2:{ unfold antitone. apply μNS_antitone. }
  specialize (μNS_inf_le_1 e) as H'. unfold μNS_inf in H'.
  rewrite H in H'. repeat match goal with
  | [ H: ∞ ≤ 1 |- _ ] => inversion H; clear H
  | [ H: ∞ < 1 |- _ ] => inversion H; clear H
  | [ H: ∞ = 1 |- _ ] => inversion H; clear H
  end.
}
2:{
  intro. rewrite lim_of_inv. apply ennr_inv_lt_infinity.
  rewrite <-inf_is_lim'. 2:{ unfold antitone. apply μNS_antitone. }
  apply NS_e.
}
generalize_has_lim. apply lim_extensionality. intro n.
assert (0 < μNS n e).
1:{
  unfold μNS_inf in NS_e.
  specialize (inf_is_glb (λ n, μNS n e)) as Q. destruct Q as [Q _].
  unfold is_lower_bound in Q. eapply ennr_lt_le_trans; [apply NS_e|].
  apply Q. repeat eexists.
}
erewrite sss_preserves_μNS.
2:{ intro. apply ktx_congruence. apply sss_sample_query. assumption. }
cbn. reflexivity.
Qed.

Fact sss_antitone_S N e :
∀ t t' e' w₁, sss (eval (S N)) t e t' e' w₁ →
∃ e₀ w₀, sss (eval N) t e t' e₀ w₀.
Proof.
apply sss_antitone_S_aux.
apply μNS_antitone_S.
Qed.

Fact stop_monotone_S N e : stop N e → stop (S N) e.
Proof.
apply stop_monotone_S_aux.
apply μNS_antitone_S.
Qed.

Fact stop_monotone N e : stop N e → ∀ N', N <= N' → stop N' e.
Proof.
intros Stop N'. induction 1.
+ apply Stop.
+ apply stop_monotone_S. assumption.
Qed.

Lemma μTV_stuck N e V :
stop N e →
(∀ v, e = exp_val v → False) →
∀ N', 0 = μTV N' e V.
Proof.
intros.
destruct (le_dec N' (S N)).
+ apply ennr_le_antisym. 1:{ apply ennr_le_0. }
  erewrite μTV_stuck_S by eassumption.
  apply μTV_monotone. omega.
+ destruct N'. 1:{ exfalso. omega. }
  apply stop_monotone with (N' := N') in H. 2:{ omega. }
  erewrite <- μTV_stuck_S by assumption.
  ring.
Qed.

Lemma μTV_sup_stuck N e V :
stop N e →
(∀ v, e = exp_val v → False) →
0 = μTV_sup e V.
Proof.
intros.
unfold μTV_sup. erewrite sup_of_constant. 1:{ reflexivity. }
intro. apply eq_sym.
eapply μTV_stuck; eassumption.
Qed.

Lemma μTV_sup_le_μNS_inf e V :
μTV_sup e V ≤ μNS_inf e.
Proof.
unfold μTV_sup, μNS_inf. apply sup_le_inf.
3:{ intro. apply μTV_le_μNS. }
2:{ repeat intro. apply μNS_antitone. omega. }
1:{ repeat intro. apply μTV_monotone. omega. }
Qed.
