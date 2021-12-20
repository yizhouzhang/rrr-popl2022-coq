Require Import Lang.Syntax.
Require Import Lang.Bindings.
Require Import Lang.Entropy.
Require Import Coq.Reals.Reals.
Require Import Lebesgue.
Require Import Coq.Reals.ROrderedType.
Require Import Lra.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

(** Semantics of built-in operations *)
Definition binop_interp (op : binop) (v1 v2 : val0) : option val0 :=
match v1, v2 with
| val_real r1, val_real r2 =>
  Some (
    match op with
    | binop_plus => val_real (r1 + r2)
    | binop_mult => val_real (r1 * r2)
    | binop_lt => val_bool (if Rlt_dec r1 r2 then true else false)
    | binop_le => val_bool (if Rle_dec r1 r2 then true else false)
    | binop_eq_real => val_bool (if Req_dec r1 r2 then true else false)
    end
  )
| _, _ => None
end.

Section section_sss.
Context (eval : entropy → exp0 → option (entropy * exp0 * R⁺)).

(** The unnormalized density of not getting stuck within [N] steps *)
Definition ρNS_aux (t : entropy) (e : exp0) : R⁺ :=
match eval t e with
| Some (_, _, w) => w
| None => 0
end.

(** The measure induced by [ρNS_aux] *)
Definition μNS_aux (e : exp0) : R⁺ :=
∫ (λ t, ρNS_aux t e) μentropy.

Reserved Notation "⟨ t | e ⟩ ⤳ ⟨ t' | e' ⟩ • w" 
  (at level 70, t, e, t', e', w at level 65).
Inductive sss : entropy → exp0 → entropy → exp0 → R⁺ → Prop :=
(* reduction rules *)
| sss_app :
  ∀ t e (v : val0),
  ⟨t|exp_app (val_fun e) v⟩ ⤳ ⟨t|V_subst_exp v e⟩ • 1
| sss_fix :
  ∀ t e,
  ⟨t|exp_app (val_fix e) val_unit⟩ ⤳ ⟨t|V_subst_exp (val_fix e) e⟩ • 1
| sss_let :
  ∀ t (v : val0) e,
  ⟨t|exp_let v e⟩ ⤳ ⟨t|V_subst_exp v e⟩ • 1
| sss_binop :
  ∀ t op (v1 v2 v : val0),
  binop_interp op v1 v2 = Some v →
  ⟨t|exp_binop op v1 v2⟩ ⤳ ⟨t|v⟩ • 1
| sss_proj :
  ∀ t (vL vR : val0) b,
  ⟨ t | exp_proj (val_pair vL vR) b ⟩ ⤳ ⟨t|if b then vL else vR⟩ • 1
| sss_then :
  ∀ t e1 e2,
  ⟨t|exp_if (val_bool true) e1 e2⟩ ⤳ ⟨t|e1⟩ • 1
| sss_else :
  ∀ t e1 e2,
  ⟨t|exp_if (val_bool false) e1 e2⟩ ⤳ ⟨t|e2⟩ • 1
| sss_sample_unif :
  ∀ t,
  let r := proj1_sig (πL t 0%nat) in
  ⟨t|exp_sample val_unif⟩ ⤳ ⟨(πR t)|val_real r⟩ • 1
| sss_sample_query :
  ∀ t e,
  0 < μNS_aux e →
  ⟨t|exp_sample (val_query e)⟩ ⤳ ⟨t|e⟩ • (/ μNS_aux e)
| sss_sample_query_exn :
  ∀ t e,
  0 = μNS_aux e →
  ⟨t|exp_sample (val_query e)⟩ ⤳ ⟨t|exp_exn⟩ • 1
| sss_score :
  ∀ t (r : R) (r_pos : (0 < r)%R),
  (r ≤ 1)%R →
  ⟨t|exp_score (val_real r)⟩ ⤳ ⟨t|val_unit⟩ • (finite r (Rlt_le _ _ r_pos))

(* structural rules *)
| sss_ktx_app1 :
  ∀ t e1 e2 t' e1' w,
  ⟨t|e1⟩ ⤳ ⟨t'|e1'⟩ • w →
  ⟨t|exp_app e1 e2⟩ ⤳ ⟨t'|exp_app e1' e2⟩ • w
| sss_ktx_app2 :
  ∀ t (v : val0) e2 t' e2' w,
  ⟨t|e2⟩ ⤳ ⟨t'|e2'⟩ • w →
  ⟨t|exp_app v e2⟩ ⤳ ⟨t'|exp_app v e2'⟩ • w
| sss_ktx_let :
  ∀ t e1 e2 t' e1' w,
  ⟨t|e1⟩ ⤳ ⟨t'|e1'⟩ • w →
  ⟨t|exp_let e1 e2⟩ ⤳ ⟨t'|exp_let e1' e2⟩ • w
| sss_ktx_binop1 :
  ∀ t op e1 e2 t' e1' w,
  ⟨t|e1⟩ ⤳ ⟨t'|e1'⟩ • w →
  ⟨t|exp_binop op e1 e2⟩ ⤳ ⟨t'|exp_binop op e1' e2⟩ • w
| sss_ktx_binop2 :
  ∀ t op (v : val0) e2 t' e2' w,
  ⟨t|e2⟩ ⤳ ⟨t'|e2'⟩ • w →
  ⟨t|exp_binop op v e2⟩ ⤳ ⟨t'|exp_binop op v e2'⟩ • w
| sss_ktx_proj :
  ∀ t e1 b t' e1' w,
  ⟨t|e1⟩ ⤳ ⟨t'|e1'⟩ • w →
  ⟨t|exp_proj e1 b⟩ ⤳ ⟨t'|exp_proj e1' b⟩ • w
| sss_ktx_if :
  ∀ t e1 e2 e3 t' e1' w,
  ⟨t|e1⟩ ⤳ ⟨t'|e1'⟩ • w →
  ⟨t|exp_if e1 e2 e3⟩ ⤳ ⟨t'|exp_if e1' e2 e3⟩ • w
| sss_ktx_sample :
  ∀ t e t' e' w,
  ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w →
  ⟨t|exp_sample e⟩ ⤳ ⟨t'|exp_sample e'⟩ • w
| sss_ktx_score :
  ∀ t e t' e' w,
  ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w →
  ⟨t|exp_score e⟩ ⤳ ⟨t'|exp_score e'⟩ • w
where "⟨ t | e ⟩ ⤳ ⟨ t' | e' ⟩ • w" := (sss t e t' e' w)
.

Hint Constructors sss : core.

Lemma ktx_congruence t e t' e' w :
⟨t | e⟩ ⤳ ⟨t' | e'⟩ • w → ∀ K, ⟨t | K[/e]⟩ ⤳ ⟨t' | K[/e']⟩ • w.
Proof.
induction K ; crush.
Qed.

Lemma sss_bifurcate t e t' e' w :
⟨t | e⟩ ⤳ ⟨t' | e'⟩ • w →
(∀ t'', ⟨t'' | e⟩ ⤳ ⟨t'' | e'⟩ • w) ∨ (
  ∃ K,
  e = K[/exp_sample val_unif] ∧
  e' = K[/val_real (proj1_sig (πL t 0%nat))] ∧
  t' = πR t ∧
  w = 1
).
Proof.
induction 1.
+ left ; clear t ; intro t ; constructor ; auto.
+ left ; clear t ; intro t ; constructor ; auto.
+ left ; clear t ; intro t ; constructor ; auto.
+ left ; clear t ; intro t ; constructor ; auto.
+ left ; clear t ; intro t ; constructor ; auto.
+ left. clear t. intro t. eapply sss_then.
+ left. clear t. intro t. eapply sss_else.
+ right ; exists ktx_hole ; crush.
+ left ; clear t ; intro t ; constructor ; auto.
+ left ; clear t ; intro t ; constructor ; auto.
+ left ; clear t ; intro t ; constructor ; auto.
+ destruct IHsss as [ | Q ] ; [ left | right ].
  1:{ intro ; constructor ; auto. }
  destruct Q as [K [? ?]].
  eexists (ktx_app1 K _) ; crush.
+ destruct IHsss as [ | Q ] ; [ left | right ].
  1:{ intro ; constructor ; auto. }
  destruct Q as [K [? ?]].
  eexists (ktx_app2 _ K) ; crush.
+ destruct IHsss as [ | Q ] ; [ left | right ].
  1:{ intro ; constructor ; auto. }
  destruct Q as [K [? ?]].
  eexists (ktx_let K _) ; crush.
+ destruct IHsss as [ | Q ] ; [ left | right ].
  1:{ intro ; constructor ; auto. }
  destruct Q as [K [? ?]].
  eexists (ktx_binop1 _ K _) ; crush.
+ destruct IHsss as [ | Q ] ; [ left | right ].
  1:{ intro ; constructor ; auto. }
  destruct Q as [K [? ?]].
  eexists (ktx_binop2 _ _ K) ; crush.
+ destruct IHsss as [ | Q ] ; [ left | right ].
  1:{ intro ; constructor ; auto. }
  destruct Q as [K [? ?]].
  eexists (ktx_proj K _) ; crush.
+ destruct IHsss as [ | Q ] ; [ left | right].
  1:{ intro. constructor. auto. }
  destruct Q as [K [? ?]].
  eexists (ktx_if K _ _) ; crush.
+ destruct IHsss as [ | Q ] ; [ left | right ].
  1:{ intro ; constructor ; auto. }
  destruct Q as [K [? ?]].
  eexists (ktx_sample K) ; crush.
+ destruct IHsss as [ | Q ] ; [ left | right ].
  1:{ intro ; constructor ; auto. }
  destruct Q as [K [? ?]].
  eexists (ktx_score K) ; crush.
Qed.

(** This lemma states that whether a term can step has nothing to do with the
entropy value. *)
Lemma stuck_test_sound e :
∀ t t' e' w, 
  ⟨t | e⟩ ⤳ ⟨t' | e'⟩ • w →
  ∀ s, ∃ s' e'' w', ⟨s | e⟩ ⤳ ⟨s' | e''⟩ • w'
.
Proof.
intros t t' e' w . induction 1 ; intros s;
try (repeat eexists; econstructor; eassumption);
try (destruct (IHsss s) as (? & ? & ? & ?); repeat eexists; constructor; eassumption).
(* 
  TODO 
  Seems that Coq can not find r_pos: (0 < r)%R in this composed tactic.
*)
Unshelve.
assumption.
Qed.

Ltac auto_sss_ktx_inv := repeat match goal with
| [ H : exp_app _ _ = _ |- _ ] => inversion H ; subst ; clear H
| [ H : exp_let _ _ = _ |- _ ] => inversion H ; subst ; clear H
| [ H : exp_binop _ _ _ = _ |- _ ] => inversion H ; subst ; clear H
| [ H : exp_proj _ _ = _ |- _ ] => inversion H ; subst ; clear H
| [ H : exp_if _ _ _ = _ |- _ ] => inversion H ; subst ; clear H
| [ H : exp_sample _ = _ |- _ ] => inversion H ; subst ; clear H
| [ H : exp_score _ = _ |- _ ] => inversion H ; subst ; clear H
| [ H : exp_exn = _ |- _ ] => inversion H ; subst ; clear H
| [ P : ∀ v, ?e = exp_val v → False, H : exp_val _ = ktx_plug _ ?e |- _ ] =>
  exfalso ; eapply P ;
  apply eq_sym in H ;
  apply ktx_plug_is_val_inv in H ;
  destruct H as [_ H] ; subst ;
  eexists
| [ H : sss _ (exp_val _) _ _ _ |- _ ] => inversion H
end.

Lemma sss_ktx_inv t Kf t' e' w :
⟨t|Kf⟩ ⤳ ⟨t'|e'⟩ • w →
∀ K f, Kf = K[/f] →
(∀ v, f = exp_val v → False) →
∃ f', ⟨t|f⟩ ⤳ ⟨t'|f'⟩ • w ∧ e' = K[/f'].
Proof.
unfold not.
induction 1 ; intros K f HKf f_not_val.
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor | reflexivity].  }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor | reflexivity].  }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor | reflexivity].  }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor ; eauto | reflexivity]. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor ; eauto | reflexivity]. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor ; eauto | reflexivity]. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor ; eauto | reflexivity]. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor ; eauto | reflexivity]. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor ; eauto | reflexivity]. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor ; eauto | reflexivity]. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  1:{ eexists ; split ; [constructor ; eauto | reflexivity]. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  { eexists ; split ; [constructor ; eauto | reflexivity]. }
  { destruct (IHsss _ _ eq_refl f_not_val) as [f' [? ?]] ; subst.
    eexists ; split ; eauto. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  { eexists ; split ; [constructor ; eauto | reflexivity]. }
  { destruct (IHsss _ _ eq_refl f_not_val) as [f' [? ?]] ; subst.
    eexists ; split ; eauto. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  { eexists ; split ; [constructor ; eauto | reflexivity]. }
  { destruct (IHsss _ _ eq_refl f_not_val) as [f' [? ?]] ; subst.
    eexists ; split ; eauto. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  { eexists ; split ; [constructor ; eauto | reflexivity]. }
  { destruct (IHsss _ _ eq_refl f_not_val) as [f' [? ?]] ; subst.
    eexists ; split ; eauto. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  { eexists ; split ; [constructor ; eauto | reflexivity]. }
  { destruct (IHsss _ _ eq_refl f_not_val) as [f' [? ?]] ; subst.
    eexists ; split ; eauto. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  { eexists ; split ; [constructor ; eauto | reflexivity]. }
  { destruct (IHsss _ _ eq_refl f_not_val) as [f' [? ?]] ; subst.
    eexists ; split ; eauto. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  { eexists ; split ; [constructor ; eauto | reflexivity]. }
  { destruct (IHsss _ _ eq_refl f_not_val) as [f' [? ?]] ; subst.
    eexists ; split ; eauto. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  { eexists ; split ; [constructor ; eauto | reflexivity]. }
  { destruct (IHsss _ _ eq_refl f_not_val) as [f' [? ?]] ; subst.
    eexists ; split ; eauto. }
+ destruct K ; simpl in HKf ; subst ; auto_sss_ktx_inv.
  { eexists ; split ; [constructor ; eauto | reflexivity]. }
  { destruct (IHsss _ _ eq_refl f_not_val) as [f' [? ?]] ; subst.
    eexists ; split ; eauto. }
Qed.

Lemma sss_ktx_exn_inv t K t' e' w :
~ ⟨t | K[/exp_exn]⟩ ⤳ ⟨t' | e'⟩ • w.
Proof.
unfold not.
induction K in t', e', w |-* ; simpl; intros H.
+ inversion H.
+ eapply sss_ktx_inv in H as [? [H ?]].
  1:{ eapply IHK. apply H. } 2:{ intros. ktx_plug_is_val_absurd. }
  bind_ktx_app1. reflexivity.
+ eapply sss_ktx_inv in H as [? [H ?]].
  1:{ eapply IHK. apply H. } 2:{ intros. ktx_plug_is_val_absurd. }
  bind_ktx_app2. reflexivity.
+ eapply sss_ktx_inv in H as [? [H ?]].
  1:{ eapply IHK. apply H. } 2:{ intros. ktx_plug_is_val_absurd. }
  bind_ktx_let. reflexivity.
+ eapply sss_ktx_inv in H as [? [H ?]].
  1:{ eapply IHK. apply H. } 2:{ intros. ktx_plug_is_val_absurd. }
  bind_ktx_binop1. reflexivity.
+ eapply sss_ktx_inv in H as [? [H ?]].
  1:{ eapply IHK. apply H. } 2:{ intros. ktx_plug_is_val_absurd. }
  bind_ktx_binop2. reflexivity.
+ eapply sss_ktx_inv in H as [? [H ?]].
  1:{ eapply IHK. apply H. } 2:{ intros. ktx_plug_is_val_absurd. }
  bind_ktx_proj. reflexivity.
+ eapply sss_ktx_inv in H as [? [H ?]].
  1:{ eapply IHK. apply H. } 2:{ intros. ktx_plug_is_val_absurd. }
  bind_ktx_if. reflexivity.
+ eapply sss_ktx_inv in H as [? [H ?]].
  1:{ eapply IHK. apply H. } 2:{ intros. ktx_plug_is_val_absurd. }
  bind_ktx_sample. reflexivity.
+ eapply sss_ktx_inv in H as [? [H ?]].
  1:{ eapply IHK. apply H. } 2:{ intros. ktx_plug_is_val_absurd. }
  bind_ktx_score. reflexivity.
Qed.
End section_sss.

Notation "eval ⟨ t | e ⟩ ⤳ ⟨ t' | e' ⟩ • w" :=
  (sss eval t e t' e' w)
  (at level 40, t, e, t', e', w at level 35).
