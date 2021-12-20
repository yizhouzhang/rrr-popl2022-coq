Require Import RRR.Lang.Syntax.
Require Import RRR.Lang.Entropy.
Require Import RRR.Lang.SmallStep.
Require Import RRR.Lang.Static RRR.Lang.StaticFacts.
Require Import RRR.Lebesgue.Lebesgue.
Require Import Coq.Reals.Reals.
Require Import Coq.omega.Omega.

Set Implicit Arguments.

Section section_determinism.
Context (eval : entropy → exp0 → option (entropy * exp0 * R⁺)).

Local Open Scope type_scope.

Fixpoint sss_dec (t : entropy) (e : exp0) {struct e} :
{ t' & { e' & { w & eval ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w } } } +
( ~ ∃ t' e' w, eval ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w ) 
.
Proof.
destruct e as [ v | e1 e2 | e1 e2 | op e1 e2 | e0 b | e1 e2 e3 | e0 | e0 | ];
unfold not in *.
+ (* Case exp_val *)
  apply inr.
  destruct 1 as [ t' [ e' [ w H ]] ].
  inversion H.
+ (* Case exp_app *)
  destruct e1 as [ [] | | | | | | | | ] eqn:H_e1;
  try match goal with
  | [ |- context[sss eval _ (exp_app (exp_val (val_fun _)) _) _ _ _ ] ] =>
    destruct e2 eqn:H_e2
  | [ |- context[sss eval _ (exp_app (exp_val (val_fix _)) _) _ _ _ ] ] =>
    destruct e2 as [ [] | | | | | | | | ] eqn:H_e2
  end ;
  try match goal with
  | [ |- context[sss eval _ (exp_app (exp_val (val_fun _)) (exp_val _)) _ _ _ ] ] =>
    (* beta *)
    left ; repeat eexists ; constructor
  | [ |- context[sss eval _ (exp_app (exp_val (val_fix _)) (exp_val val_unit)) _ _ _ ] ] =>
    (* fixpoint beta *)
    left ; repeat eexists ; constructor
  | [ |- context[sss eval _ (exp_app (exp_val _) _) _ _ _ ] ] =>
    (* structural right *)
    specialize (sss_dec t e2) ; try subst e2 ; 
    destruct sss_dec as [ [t'[e'[w H]]] | ] ; [
      left ; repeat eexists ; apply sss_ktx_app2 ; eassumption |
      right ; destruct 1 as [t'[e'[w H]]] ;
      repeat match goal with
      | [ H : sss eval _ (exp_app (exp_val _) _) _ _ _ |- _ ] =>
        inversion H ; subst ; clear H
      | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
        inversion H ; subst ; clear H
      | [ H : _ → False |- False ] => apply H ; repeat eexists ; eassumption
      end
    ]
  | [ |- context[sss eval _ (exp_app _ _) _ _ _ ] ] =>
    (* structural left *)
    specialize (sss_dec t e1) ; subst e1 ;
    destruct sss_dec as [ [t'[e'[w H]]] | ] ; [
      left ; repeat eexists ; apply sss_ktx_app1 ; eassumption |
      right ; destruct 1 as [t'[e'[w H]]] ;
      repeat match goal with
      | [ H : sss eval _ (exp_app _ _) _ _ _, IH : _ → False |- False ] =>
        inversion H ; subst ; clear H;
        apply IH ; repeat eexists ; eassumption
      end
    ]
  end.
+ (* Case exp_let *)
  destruct e1 as [ v | | | | | | | | ] eqn:H_e1 ;
  try match goal with
  | [ |- context[sss eval _ (exp_let (exp_val _) _) _ _ _ ] ] =>
    (* reduction *)
    left ; repeat eexists ; constructor
  end ;
  match goal with
  | [ |- context[sss eval _ (exp_let _ _) _ _ _ ] ] =>
    (* structural *)
    specialize (sss_dec t e1) ; subst e1 ;
    destruct sss_dec as [ [t'[e'[w H]]] | ] ; [
      left ; repeat eexists ; apply sss_ktx_let ; eassumption |
      right ; destruct 1 as [t'[e'[w H]]] ;
      repeat match goal with
      | [ H : sss eval _ (exp_let _ _) _ _ _, IH : _ → False |- False ] =>
        inversion H ; subst ; clear H;
        apply IH ; repeat eexists ; eassumption
      end
    ]
  end.
+ (* Case exp_binop *)
  destruct e1 as [ v1 | | | | | | | | ] eqn:H_e1;
  try match goal with
  | [ |- context[sss eval _ (exp_binop _ (exp_val _) _) _ _ _ ] ] =>
    destruct e2 as [ v2 | | | | | | | | ] eqn:H_e2;
    try match goal with
    | [ |- context[sss eval _ (exp_binop _ (exp_val _) (exp_val _)) _ _ _ ] ] =>
      (* reduction (see below) *)
      idtac
    | [ |- context[sss eval _ (exp_binop _ (exp_val _) _) _ _ _ ] ] =>
      (* structural right *)
      specialize (sss_dec t e2) ; subst e2 ;
      destruct sss_dec as [ [t'[e'[w H]]] | ] ; [
        left ; repeat eexists ; apply sss_ktx_binop2 ; eassumption |
        right ; destruct 1 as [t'[e'[w H]]] ;
        repeat match goal with
        | [ H : sss eval _ (exp_binop _ (exp_val _) _) _ _ _ |- _ ] =>
          inversion H ; subst ; clear H
        | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
          inversion H ; subst ; clear H
        | [ H : _ → False |- False ] => apply H ; repeat eexists ; eassumption
        end
      ]
    end
  | [ |- context[sss eval _ (exp_binop _ _ _) _ _ _ ] ] =>
    (* structural left *)
    specialize (sss_dec t e1) ; subst e1 ;
    destruct sss_dec as [ [t'[e'[w H]]] | ] ; [
      left ; repeat eexists ; apply sss_ktx_binop1 ; eassumption |
      right ; destruct 1 as [t'[e'[w H]]] ;
      repeat match goal with
      | [ H : sss eval _ (exp_binop _ _ _) _ _ _, IH : _ → False |- False ] =>
        inversion H ; subst ; clear H;
        apply IH ; repeat eexists ; eassumption
      end
    ]
  end.
  {
    destruct (binop_interp op v1 v2) eqn:Hop.
    + left; repeat eexists; apply sss_binop; eassumption.
    + right; destruct 1 as [t'[e'[w H]]];
      repeat match goal with
      | [ H : sss eval _ (exp_binop _ _ _) _ _ _ |- False ] =>
        inversion H ; subst ; clear H
      | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
        inversion H
      end.
      rewrite Hop in *; discriminate.
  }
+ (* Case exp_proj *)
  destruct e0 as [ [] | | | | | | | | ] eqn:H_e0;
  try match goal with
  | [ |- context[sss eval _ (exp_proj (exp_val (val_pair _ _)) _) _ _ _ ] ] =>
    (* reduction (see below) *)
    idtac
  | [ |- context[sss eval _ (exp_proj (exp_val _) _) _ _ _ ] ] =>
    (* stuck *)
    right ; destruct 1 as [t'[e'[w H]]] ;
    repeat match goal with
    | [ H : sss eval _ (exp_proj (exp_val _) _) _ _ _ |- False ] =>
      inversion H ; subst ; clear H
    | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
      inversion H
    end
  | [ |- context[sss eval _ (exp_proj _ _) _ _ _ ] ] =>
    (* structural *)
    specialize (sss_dec t e0) ; subst e0 ;
    destruct sss_dec as [ [t'[e'[w H]]] | ] ; [
      left ; repeat eexists ; apply sss_ktx_proj ; eassumption |
      right ; destruct 1 as [t'[e'[w H]]] ;
      repeat match goal with
      | [ H : sss eval _ (exp_proj _ _) _ _ _, IH : _ → False |- False ] =>
        inversion H ; subst ; clear H;
        apply IH ; repeat eexists ; eassumption
      end
    ]
  end.
  left; repeat eexists; apply sss_proj.
+ (* Case exp_if *)
  destruct e1 as [ [] | | | | | | | | ] eqn:H_e1;
  try match goal with
  | [ |- context[sss eval _ (exp_if (exp_val (val_bool _)) _ _) _ _ _ ] ] =>
    (* reduction (see below) *)
    idtac
  | [ |- context[sss eval _ (exp_if (exp_val _) _ _) _ _ _ ] ] =>
    (* stuck *)
    right ; destruct 1 as [t'[e'[w H]]] ;
    repeat match goal with
    | [ H : sss eval _ (exp_if (exp_val _) _ _) _ _ _ |- False ] =>
      inversion H ; subst ; clear H
    | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
      inversion H
    end
  | [ |- context[sss eval _ (exp_if _ _ _) _ _ _ ] ] =>
    (* structural *)
    specialize (sss_dec t e1) ; subst e1 ;
    destruct sss_dec as [ [t'[e'[w H]]] | ] ; [
      left ; repeat eexists ; apply sss_ktx_if ; eassumption |
      right ; destruct 1 as [t'[e'[w H]]] ;
      repeat match goal with
      | [ H : sss eval _ (exp_if _ _ _) _ _ _, IH : _ → False |- False ] =>
        inversion H ; subst ; clear H;
        apply IH ; repeat eexists ; eassumption
      end
    ]
  end.
  destruct b as [ | ]; left; repeat eexists; constructor.
+ (* Case exp_sample *)
  destruct e0 as [ [] | | | | | | | | ] eqn:H_e0;
  try match goal with
  | [ |- context[sss eval _ (exp_sample (exp_val val_unif)) _ _ _ ] ] =>
    (* Case sample Uniform *)
    idtac (* see below *)
  | [ |- context[sss eval _ (exp_sample (exp_val (val_query _))) _ _ _ ] ] =>
    (* Case sample (query e) *)
    idtac (* see below *)
  | [ |- context[sss eval _ (exp_sample (exp_val _)) _ _ _ ] ] =>
    (* stuck *)
    right ; destruct 1 as [t'[e'[w H]]] ;
    repeat match goal with
    | [ H : sss eval _ (exp_sample (exp_val _)) _ _ _ |- False ] =>
      inversion H ; subst ; clear H
    | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
      inversion H
    end
  | [ |- context[sss eval _ (exp_sample _) _ _ _ ] ] =>
    (* structural *)
    specialize (sss_dec t e0) ; subst e0 ;
    destruct sss_dec as [ [t'[e'[w H]]] | ] ; [
      left ; repeat eexists ; apply sss_ktx_sample ; eassumption |
      right ; destruct 1 as [t'[e'[w H]]] ;
      repeat match goal with
      | [ H : sss eval _ (exp_sample _) _ _ _, IH : _ → False |- False ] =>
        inversion H ; subst ; clear H;
        apply IH ; repeat eexists ; eassumption
      end
    ]
  end.
  { left; repeat eexists; apply sss_sample_unif; assumption. }
  {
    destruct (ennr_0_lt_dec (μNS_aux eval e))%ennr as [HNS|HNS].
    - left ; repeat eexists ; apply sss_sample_query ; crush.
    - left ; repeat eexists ; apply sss_sample_query_exn ; crush.
  }
+ (* Case exp_score *)
  destruct e0 as [ [] | | | | | | | | ] eqn:H_e0;
  try match goal with
  | [ |- context[sss eval _ (exp_score (exp_val (val_real _))) _ _ _ ] ] =>
    (* reduction (see below) *)
    idtac
  | [ |- context[sss eval _ (exp_score (exp_val _)) _ _ _ ] ] =>
    (* stuck *)
    right ; destruct 1 as [t'[e'[w H]]] ;
    repeat match goal with
    | [ H : sss eval _ (exp_score (exp_val _)) _ _ _ |- False ] =>
      inversion H ; subst ; clear H
    | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
      inversion H
    end
  | [ |- context[sss eval _ (exp_score _) _ _ _ ] ] =>
    (* structural *)
    specialize (sss_dec t e0) ; subst e0 ;
    destruct sss_dec as [ [t'[e'[w H]]] | ] ; [
      left ; repeat eexists ; apply sss_ktx_score ; eassumption |
      right ; destruct 1 as [t'[e'[w H]]] ;
      repeat match goal with
      | [ H : sss eval _ (exp_score _) _ _ _, IH : _ → False |- False ] =>
        inversion H ; subst ; clear H;
        apply IH ; repeat eexists ; eassumption
      end
    ]
  end.
  destruct (Rlt_dec 0 r), (Rle_dec r 1).
  - left; repeat eexists; unshelve apply sss_score; assumption.
  - right ; destruct 1 as [t'[e'[w H]]] ; inversion H ; subst ;
    try match goal with
    | [ _: ?P, _: ¬ ?P |- False ] =>
      auto
    | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
      inversion H
    end.
  - right ; destruct 1 as [t'[e'[w H]]] ; inversion H ; subst ;
    try match goal with
    | [ _: ?P, _: ¬ ?P |- False ] =>
      auto
    | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
      inversion H
    end.
  - right ; destruct 1 as [t'[e'[w H]]] ; inversion H ; subst ;
    try match goal with
    | [ _: ?P, _: ¬ ?P |- False ] =>
      auto
    | [ H : sss eval _ (exp_val _) _ _ _ |- _ ] =>
      inversion H
    end.
+ (* Case exp_exn *) 
  right. destruct 1 as [t'[e'[w H]]]. inversion H.
Qed.

Ltac auto_unique := repeat match goal with
| [ H : sss eval _ (exp_val _) _ _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : sss eval _ (exp_app _ _) _ _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : sss eval _ (exp_let _ _) _ _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : sss eval _ (exp_binop _ _ _) _ _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : sss eval _ (exp_proj _ _) _ _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : sss eval _ (exp_if _ _ _) _ _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : sss eval _ (exp_sample _) _ _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : sss eval _ (exp_score _) _ _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : sss eval _ exp_exn _ _ _ |- _ ] => inversion H ; subst ; clear H
| [ IH : ∀ _ _ _, _ → _, H : sss eval _ _ ?T' _ _ |- _ = ?T' ∧ _ ∧ _ ] =>
  apply IH in H
| [ H1 : ?x = ?y, H2 : ?x < ?y |- _ ] =>
  rewrite H1 in H2 ; exfalso ; apply ennr_lt_irrefl in H2 ; exact H2
| [ H : match ?x with _ => _ end, H' : 0 = ?x |- _ ] =>
  rewrite <- H' in H ; simpl in H
| [ H : _ ∨ _ |- _ ] =>
  destruct H
end.

Lemma sss_unique t e T E W :
eval ⟨t|e⟩ ⤳ ⟨T|E⟩ • W →
∀ T' E' W',  
  eval ⟨t|e⟩ ⤳ ⟨T'|E'⟩ • W' →
T = T' ∧ E = E' ∧ W = W'.
Proof.
induction 1 ; intros ; auto_unique ; crush.
Defined.

Lemma sss_det t e :
{ t' & { e' & { w &
  eval ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w *
  ∀ _t' _e' _w, eval ⟨t|e⟩ ⤳ ⟨_t'|_e'⟩ • _w → _t' = t' ∧ _e' = e' ∧ _w = w
} } } +
( ~ ∃ t' e' w, eval ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w ).
Proof.
destruct (sss_dec t e) as [ H | H ]; [ left | right ; exact H ].
destruct H as [t'[e'[w H]]].
do 3 eexists. 
split ; [ exact H | ].
intros.
eapply sss_unique in H ; eassumption.
Defined.

End section_determinism.

Fixpoint eval
(N : nat) (t : entropy) (e : exp0) {struct N} : option (entropy * exp0 * R⁺).
Proof.
destruct N as [ | N' ].
+ refine (Some (t, e, 1)).
+ destruct (exp_val_dec e).
  1:{ refine (Some (t, e, 1)). }
  destruct (exp_ktx_exn_dec e).
  1:{ refine (Some (t, e, 1)). }
  destruct (sss_det (eval N') t e) as [ H | ] ; [ | right ]. (* eval level decrease*)
  destruct H as [t'[e'[w' ?]]].
  destruct (eval N' t' e') as [ [[t'' e''] w''] | ] ; [ left | right ]. (* eval step decrease *)
  refine (t'', e'', w' * w'').
Defined.

(** [e] is stuck at index [N]. *)
Definition stop N e : Prop :=
(∀ t t' e' w, (eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w → False) ∧
(∀ K, e =  K[/exp_exn] → False).

(** Useless lemmas for readability BEG *)

Notation "evaln ⟨ t | e ⟩ ↯" :=
  (evaln t e = None)
  (at level 40, t, e at level 35, only parsing).

Notation "evaln ⟨ t | e ⟩ ↘ ⟨ t' | e' ⟩ • w" :=
  (evaln t e = @Some (entropy * exp0 * R⁺) (t', e', w%ennr))
  (at level 40, t, e, t', e', w at level 35, only parsing).

Lemma eval_stop σ e : 
  eval 0 ⟨σ|e⟩ ↘ ⟨σ|e⟩ • 1
.
Proof.
  reflexivity.
Qed.

Lemma eval_val n σ (v : val0) : 
  eval (S n) ⟨σ|v⟩ ↘ ⟨σ|exp_val v⟩ • 1
.
Proof.
  reflexivity.
Qed.

Lemma eval_exn n σ K : 
  eval (S n) ⟨σ|K[/exp_exn]⟩ ↘ ⟨σ|K[/exp_exn]⟩ • 1
.
Proof.
  cbn. destruct (exp_val_dec) as [[? ->] | ?].
  { reflexivity. }
  cbn. destruct exp_ktx_exn_dec as [[? ->] | contra].
  { reflexivity. }
  contradiction (contra K).
  reflexivity.
Qed.

Lemma eval_step n σ e σ' e' w:
  eval n ⟨σ|e⟩ ⤳ ⟨σ'|e'⟩ • w →
  match eval n σ' e' with
  | Some (σ'', e'', w') => 
      eval (S n) ⟨σ|e⟩ ↘ ⟨σ''|e''⟩ • (w * w')
  | None => 
      eval (S n) ⟨σ|e⟩ ↯
  end
.
Proof.
  intros Hsss. cbn.
  destruct exp_val_dec as [[v ->] | ].
  - inversion Hsss.
  - destruct (exp_ktx_exn_dec e) as [[K ->]|].
    + apply sss_ktx_exn_inv in Hsss. contradiction.
    + destruct (sss_det (eval n) σ e) as[(? & ? & ? & ? & unique)| Hstuck].
      * apply unique in Hsss as (<- & <- & <-); cbn.
        destruct eval as [ [[? ?] ?] | ]; reflexivity.
      * contradiction Hstuck.
        repeat eexists.
        eassumption.
Qed.

Lemma eval_step_Some n σ e σ' e' σ'' e'' w w':
  eval n ⟨σ|e⟩ ⤳ ⟨σ'|e'⟩ • w →
  eval    n  ⟨σ'|e'⟩ ↘ ⟨σ''|e''⟩ • w' →
  eval (S n) ⟨σ |e ⟩ ↘ ⟨σ''|e''⟩ • (w * w')
.
Proof.
  intros Hsss%eval_step Hevaln.
  rewrite Hevaln in Hsss.
  assumption.
Qed.

Lemma eval_step_None n σ e σ' e' w:
  eval n ⟨σ|e⟩ ⤳ ⟨σ'|e'⟩ • w →
  eval    n  ⟨σ'|e'⟩ ↯ →
  eval (S n) ⟨σ |e ⟩ ↯
.
Proof.
  intros Hsss%eval_step Hevaln.
  rewrite Hevaln in Hsss.
  assumption.
Qed.

(** Useless lemmas for readability END *)

Lemma sss_eval N t e t' e' w :
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w →
eval (S N) t e = match eval N t' e' with
                 | Some (p, w') => Some (p, w * w')
                 | None => None
                 end.
Proof.
intro Hsss.
simpl eval.
destruct (exp_val_dec e) as [ [v Hv] | ].
1: { subst ; inversion Hsss. }
destruct (exp_ktx_exn_dec e) as [ [K HK] | ].
1:{ subst. exfalso. apply sss_ktx_exn_inv in Hsss. trivial. }
destruct (sss_det (eval N) t e) as [[_t'[_e'[_w[_Hsss Unique]]]] | H ].
2: { exfalso ; apply H ; repeat eexists ; apply Hsss. }
apply Unique in Hsss ; destruct Hsss as [? []] ; subst.
repeat match goal with
| [ |- context[ match ?x with _ => _ end ] ] => destruct x
end ; reflexivity.
Qed.

Lemma eval_O t e :
eval O t e = Some (t, e, 1).
Proof.
reflexivity.
Qed.

Lemma eval_val_S N t (v : val0) :
eval (S N) t v = Some (t, exp_val v, 1).
Proof.
reflexivity.
Qed.

Lemma eval_ktx_exn N t K :
eval N t (K[/exp_exn]) = Some (t, K[/exp_exn], 1).
Proof.
induction N.
+ simpl ; reflexivity.
+ simpl.
  destruct (exp_val_dec (K[/exp_exn])) as [ [v Hv] | H' ].
  1:{
    apply ktx_plug_is_val_inv in Hv.
    destruct Hv as [? Hv] ; inversion Hv.
  }
  clear H'.
  destruct (exp_ktx_exn_dec (K[/exp_exn])) as [ [? ?] | H'' ].
  1:{ reflexivity. }
  exfalso. eapply H''. reflexivity.
Qed.

Lemma fold_eval_from_sss N t e t' e' w t'' e'' w':
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w →
eval    N  t' e' = Some (t'', e'', w') →
eval (S N) t  e  = Some (t'', e'', w * w').
Proof.
intros Hsss Heval.
simpl.
destruct (exp_val_dec e) as [ [v Hv] | ].
1:{ subst. inversion Hsss. }
destruct (exp_ktx_exn_dec e) as [ [K ?] | ].
1:{ subst. exfalso. apply sss_ktx_exn_inv in Hsss. trivial. }
destruct (sss_det (eval N) t e) as [[_t'[_e'[_w[_Hsss Unique]]]] | H ].
2:{
  exfalso ; apply H.
  do 3 eexists ; apply Hsss.
}
apply Unique in Hsss ; destruct Hsss as [? [? ?]] ; subst.
rewrite Heval.
reflexivity.
Qed.

Section section_unfold_eval_S_to_Some.
Local Open Scope type_scope.

Lemma unfold_eval_S_to_Some N t e t' e' w :
eval (S N) t e = Some (t', e', w) →
(∃ v, e = exp_val v   ∧ t' = t ∧ w = 1) +
(∃ K, e = K[/exp_exn] ∧ t' = t ∧ w = 1) +
{ t'' & { e'' & { w' & (eval N) ⟨t|e⟩ ⤳ ⟨t''|e''⟩ • w' *
  (∃ w'', w = w' * w'' ∧ eval N t'' e'' = Some (t', e', w''))%ennr
} } }.
Proof.
intro H.
simpl eval in H.
destruct (exp_val_dec e) as [ [v Hv] | e_not_val ] ; [ left; left | ].
1:{ subst. inversion H; subst. repeat eexists. }
destruct (exp_ktx_exn_dec e) as [ [K ?] | ? ]; [ left; right | right ].
1:{ subst. inversion H; subst. repeat eexists. }
destruct (sss_det (eval N) t e) as [ [t'' [e'' [w' [Hsss Unique]]]] | ].
2:{ inversion H. }
do 3 eexists.
split ; [ exact Hsss | ].
destruct (eval N t'' e'') as [ [[_t' _e'] w''] | ].
2:{ inversion H. }
inversion H ; subst ; clear H.
eexists.
split ; reflexivity.
Qed.
End section_unfold_eval_S_to_Some.

Lemma sss_exp_dec N e :
(∀ t, ∃ t' e' w, (eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w) ∨
(∀ t t' e' w,  ~ (eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w).
Proof.
destruct (sss_dec (eval N) entropy0 e) as [Q|Q].
+ left.
  destruct Q as [t' [e' [w Hsss]]].
  apply sss_bifurcate in Hsss.
  intro t.
  destruct Hsss as [ Hsss | [K [? [? [? ?]]]] ].
  - repeat eexists; eauto.
  - subst. repeat eexists. 
    apply ktx_congruence.
    econstructor.
  + right.
    do 4 intro; intro Hsss.
    apply Q, (stuck_test_sound Hsss). 
Qed.

Fixpoint ktx_plug_is_K_exn_inv J e K
(NotVal_e : ∀ v, e = exp_val v → False)
(Q: J[/e] = K[/exp_exn]) {struct K} :
∃ K', K = ktx_comp J K' ∧ e =  K'[/exp_exn].
Proof.
destruct K; simpl in Q.
+ destruct J; simpl in Q; inversion Q; subst. repeat eexists.
+ destruct J; simpl in Q; inversion Q; subst.
  - repeat eexists.
  - match goal with [ H : ktx_plug _ _ = ktx_plug K exp_exn |- _ ] =>
      apply ktx_plug_is_K_exn_inv in H as [? [? ?]]; [subst|apply NotVal_e]
    end.
    repeat eexists.
  - ktx_plug_is_val_absurd.
+ destruct J; simpl in Q; inversion Q; subst.
  - repeat eexists.
  - apply ktx_plug_is_val_inv in H0 as [? ?]; subst; simpl in *.
    exfalso. eapply NotVal_e. reflexivity.
  - match goal with [ H : ktx_plug _ _ = ktx_plug K exp_exn |- _ ] =>
      apply ktx_plug_is_K_exn_inv in H as [? [? ?]]; [subst|apply NotVal_e]
    end.
    repeat eexists.
+ destruct J; simpl in *; inversion Q; subst.
  - repeat eexists.
  - match goal with [ H : ktx_plug _ _ = ktx_plug K exp_exn |- _ ] =>
      apply ktx_plug_is_K_exn_inv in H as [? [? ?]]; [subst|apply NotVal_e]
    end.
    repeat eexists.
+ destruct J; simpl in *; inversion Q; subst.
  - repeat eexists.
  - match goal with [ H : ktx_plug _ _ = ktx_plug K exp_exn |- _ ] =>
      apply ktx_plug_is_K_exn_inv in H as [? [? ?]]; [subst|apply NotVal_e]
    end.
    repeat eexists.
  - ktx_plug_is_val_absurd.
+ destruct J; simpl in Q; inversion Q; subst.
  - repeat eexists.
  - apply ktx_plug_is_val_inv in H1 as [? ?]; subst; simpl in *.
    exfalso. eapply NotVal_e. reflexivity.
  - match goal with [ H : ktx_plug _ _ = ktx_plug K exp_exn |- _ ] =>
      apply ktx_plug_is_K_exn_inv in H as [? [? ?]]; [subst|apply NotVal_e]
    end.
    repeat eexists.
+ destruct J; simpl in *; inversion Q; subst.
  - repeat eexists.
  - match goal with [ H : ktx_plug _ _ = ktx_plug K exp_exn |- _ ] =>
      apply ktx_plug_is_K_exn_inv in H as [? [? ?]]; [subst|apply NotVal_e]
    end.
    repeat eexists.
+ destruct J; simpl in Q; inversion Q; subst.
  - repeat eexists.
  - match goal with [ H : ktx_plug _ _ = ktx_plug K exp_exn |- _ ] =>
      apply ktx_plug_is_K_exn_inv in H as [? [? ?]]; [subst|apply NotVal_e]
    end.
    repeat eexists; eapply ktx_plug_is_K_exn_inv; auto; exact Q.
+ destruct J; simpl in *; inversion Q; subst.
  - repeat eexists.
  - match goal with [ H : ktx_plug _ _ = ktx_plug K exp_exn |- _ ] =>
      apply ktx_plug_is_K_exn_inv in H as [? [? ?]]; [subst|apply NotVal_e]
    end.
    repeat eexists.
+ destruct J; simpl in *; inversion Q; subst.
  - repeat eexists.
  - match goal with [ H : ktx_plug _ _ = ktx_plug K exp_exn |- _ ] =>
      apply ktx_plug_is_K_exn_inv in H as [? [? ?]]; [subst|apply NotVal_e]
    end.
    repeat eexists.
Qed.

Lemma ktx_preserves_stuck N e :
(∀ v, e = exp_val v → False) → (stop N e) →
∀ K, stop N (K[/e]).
Proof.
unfold stop. intros Nonval_e Stop_e_N. intro K.
destruct Stop_e_N as [Sss_False Exn_False].
split.
+ do 4 intro; intro Step_Ke_N.
  eapply sss_ktx_inv in Step_Ke_N as [? [? ?]];
    try reflexivity; try apply Nonval_e.
  eapply Sss_False; eauto.
+ intros J Q.
  apply ktx_plug_is_K_exn_inv in Q as [? [? ?]]. 2:{ apply Nonval_e. }
  subst. eapply Exn_False. reflexivity.
Qed.

Lemma eval_None_ktx_plug N t e K :
eval N t     e   = None →
eval N t (K[/e]) = None.
Proof.
generalize t e K; clear-N; induction N as [|N IHN]; intros t e K H.
1:{ cbn in H. inversion H. }
cbn in H|-*.

destruct (exp_val_dec e) as [ [v Hv] | NotVal_e ].
1:{ inversion H. }
destruct (exp_val_dec (ktx_plug K e)) as [[? Q]|Notval_Ke].
1:{ ktx_plug_is_val_absurd. subst. eapply NotVal_e; eauto. }

destruct (exp_ktx_exn_dec e) as [ [J ?] | NotExn_e ].
1:{ inversion H. }
destruct (exp_ktx_exn_dec (ktx_plug K e)) as [ [J Q] | NotExn_Ke ].
1:{
  exfalso. clear- NotVal_e NotExn_e Q.
  apply ktx_plug_is_K_exn_inv in Q as [K' [? ?]]. 2:{ apply NotVal_e. }
  subst. eapply NotExn_e. reflexivity.
}

destruct (sss_det (eval N) t e) as [ [t'' [e'' [w' [Hsss Unique]]]] | Stop_e ].
+ destruct (sss_det (eval N) t (K[/e])) as [ [t''_ [e''_ [w'_ [Hsss_ Unique_]]]] | ].
  2:{ trivial. }
  eapply sss_ktx_inv in Hsss_ as [? [Hsss_ ?]]; try reflexivity; try assumption. subst.
  apply Unique in Hsss_ as [? [? ?]]. subst.
  destruct (eval N t'' e'') as [[[? ?] ?]|] eqn:Eval_e''. 1:{ inversion H. }
  rewrite IHN. 1:{ trivial. } apply Eval_e''.
+ destruct (sss_det (eval N) t (K[/e])) as [ [t''_ [e''_ [w'_ [Hsss_ Unique_]]]] | ].
  2:{ trivial. }
  exfalso. eapply sss_ktx_inv in Hsss_ as [? [? ?]]; try reflexivity; try assumption.
  subst. apply Stop_e. repeat eexists. eassumption.
Qed.

Lemma eval_Some_ktx_plug N : ∀ t e t' e' w K,
eval N t e = Some (t', e', w) →
(∀ v : val0, e' = v → False) →
eval N t (K[/e]) = Some (t', K[/e'], w).
Proof.
induction N as [|N IHN]; do 6 intro; intros H Notval_e.
1:{ cbn in H |- *. inversion H. subst. reflexivity. }
cbn in H|-*.

destruct (exp_val_dec e) as [ [v Hv] | NotVal_e ].
1:{ exfalso. inversion H. subst. eapply Notval_e; eauto. }
destruct (exp_val_dec (ktx_plug K e)) as [[? Q]|Notval_Ke].
1:{ exfalso. ktx_plug_is_val_absurd. subst. eapply NotVal_e; eauto. }

destruct (exp_ktx_exn_dec e) as [ [J ?] | NotExn_e ].
1:{
  inversion H; subst.
  destruct (exp_ktx_exn_dec (ktx_plug K (ktx_plug J exp_exn))) as [|NotExn_KJe].
  1:{ reflexivity. }
  exfalso. eapply NotExn_KJe. rewrite ktx_plug_comp. reflexivity.
}
destruct (exp_ktx_exn_dec (ktx_plug K e)) as [[J Q]|NotExn_Ke].
1:{
  exfalso.
  apply ktx_plug_is_K_exn_inv in Q as [K' [? ?]]. 2:{ apply NotVal_e. }
  subst. eapply NotExn_e. reflexivity.
}

destruct (sss_det (eval N) t e) as [ [t'' [e'' [w' [Hsss Unique]]]] | Stop_e ].
2:{ inversion H. }
destruct (sss_det (eval N) t (ktx_plug K e)) as [ [t''_ [e''_ [w'_ [Hsss_ Unique_]]]] | Q ].
2:{ exfalso. apply Q. repeat eexists. apply ktx_congruence. apply Hsss. }
eapply sss_ktx_inv in Hsss_ as [? [Hsss_ ?]]; try reflexivity; try assumption. subst.
apply Unique in Hsss_ as [? [? ?]]. subst.
destruct (eval N t'' e'') as [[[? ?] ?]|] eqn:Eval_e''. 2:{ inversion H. }
inversion H; subst.
erewrite IHN; try reflexivity; try assumption.
Qed.

Notation ρNS N := (ρNS_aux (eval N)).
Notation μNS N := (μNS_aux (eval N)).

(** Similar to [eval], but returns [None] if [e] does not terminate to a
value within [N] steps. It also returns the step index at which [e]
terminates. *)
Fixpoint ev2v
(N : nat) (t : entropy) (e : exp0) {struct N} : option (nat * entropy * val0 * R⁺).
Proof.
destruct N as [ | N' ].
* destruct (exp_val_dec e) as [ [v ?] | Nonval_e ].
  + refine (Some (0%nat, t, v, 1)).
  + right.
* destruct (exp_val_dec e) as [ [v ?] | Nonval_e ].
  + refine (Some (0%nat, t, v, 1)).
  + destruct (sss_det (eval N') t e) as [ H | ] ; [ | right ]. (* eval level decrease*)
    destruct H as [t'[e'[w' ?]]].
    destruct (ev2v N' t' e') as [ [[[k t''] e''] w''] | ] ; [ left | right ]. (* eval step decrease *)
    refine (S k, t'', e'', w' * w'').
Defined.

(** Useless lemmas for readability BEG *)

Notation "eval ⟨ t | e ⟩ ↯" :=
  (eval t e = None)
  (at level 40, t, e at level 35, only parsing).

Notation "ev2vn ⟨ t | e ⟩ ↘ k ⟨ t' | v ⟩ • w" :=
  (ev2vn t e = @Some (nat * entropy * val0 * R⁺) (k%nat, t', v, w%ennr))
  (at level 40, t, e, k, t', v, w at level 35, only parsing).

Lemma ev2v_val n σ (v : val0): 
  (ev2v n) ⟨σ|v⟩ ↘ 0 ⟨σ|v⟩ • 1
.
Proof.
  destruct n; reflexivity.
Qed.

Lemma ev2v_val_inverse n σ e (σ'' : entropy) (v : val0) w'' : 
  ev2v n ⟨σ|e⟩ ↘ O ⟨σ''|v⟩ • w'' →
    e = exp_val v ∧ 
    σ'' = σ ∧ 
    w'' = 1
.
Proof.
  destruct n; cbn; destruct exp_val_dec as [[? ->]|].
  1-3: (intros [=]; subst; auto).
  destruct sss_det as [(? & ? & ? & Hsss & unique)| contra].
  - destruct ev2v as [[[[? ?] ?] ?] |]; intros [=].
  - intros [=].
Qed.

Lemma ev2v_step n σ e σ' e' w : 
  eval n ⟨σ|e⟩ ⤳ ⟨σ'|e'⟩ • w →
  match ev2v n σ' e' with
  | Some (k, σ'', v, w' ) =>
      ev2v (S n) ⟨σ |e ⟩ ↘ (S k) ⟨σ''|v⟩ • (w * w')
  | None =>
      ev2v (S n) ⟨σ |e ⟩ ↯
  end
.
Proof.
  intros Hsss. 
  cbn; destruct exp_val_dec as [[? ->]|].
  { inversion Hsss. }
  destruct sss_det as [(? & ? & ? & Hsss' & unique) | contra].
  - apply unique in Hsss as (<- & <- & <-).
    destruct ev2v as [ [[[? ?] ?] ?] |]; reflexivity.
  - contradiction contra.
    repeat eexists.
    eassumption.
Qed. 

Lemma ev2v_step_None n σ e σ' e' w σ'' v w' k: 
  eval n ⟨σ|e⟩ ⤳ ⟨σ'|e'⟩ • w →
  ev2v    n  ⟨σ'|e'⟩ ↘    k  ⟨σ''|v⟩ • w' →
  ev2v (S n) ⟨σ |e ⟩ ↘ (S k) ⟨σ''|v⟩ • (w * w')
.
Proof.
  intros Hsss%ev2v_step Hrec.
  rewrite Hrec in Hsss.
  assumption. 
Qed. 

Lemma ev2v_step_Some n σ e σ' e' w σ'' v w' k: 
  eval n ⟨σ|e⟩ ⤳ ⟨σ'|e'⟩ • w →
  ev2v    n  ⟨σ'|e'⟩ ↘    k  ⟨σ''|v⟩ • w' →
  ev2v (S n) ⟨σ |e ⟩ ↘ (S k) ⟨σ''|v⟩ • (w * w')
.
Proof.
  intros Hsss%ev2v_step Hrec.
  rewrite Hrec in Hsss.
  assumption. 
Qed. 

Lemma ev2v_step_inverse n σ e σ'' v w'' k: 
  ev2v (S n) ⟨σ|e⟩ ↘ (S k) ⟨σ''|v⟩ • (w'') →
  { σ' & { e' & { w & { w' & 
    (eval n ⟨σ |e ⟩ ⤳ ⟨σ'|e'⟩ • w) ∧
    (ev2v n ⟨σ'|e'⟩ ↘ k ⟨σ''|v ⟩ • w') ∧ 
    w * w' = w''
  }}}}  
.
Proof.
  cbn; destruct exp_val_dec as [[? ->]|].
  { intros [=]. }
  destruct sss_det as [(? & ? & ? & Hsss' & unique) | contra]; [|intros [=]].
  destruct ev2v as [ [[[? ?] ?] ?] |] eqn:?; [|intros [=]].
  intros H. inversion H. subst.
  repeat eexists; eassumption.
Qed. 

(** Useless lemmas for readability END *)

Lemma unfold_ev2v_val N t (v : val0) :
ev2v N t v = Some (0%nat, t, v, 1).
Proof.
destruct N; reflexivity.
Qed.

Section section_unfold_ev2v_S_to_Some.
Local Open Scope type_scope.

Lemma unfold_ev2v_S_to_Some N t e k t' v w :
ev2v (S N) t e = Some (k, t', v, w) →
(k = 0%nat ∧ e = exp_val v ∧ t' = t ∧ w = 1) +
{ k' & { t'' & { e'' & { w' & (eval N) ⟨t|e⟩ ⤳ ⟨t''|e''⟩ • w' * ((k = S k') *
  (∃ w'', w = w' * w'' ∧ ev2v N t'' e'' = Some (k', t', v, w''))%ennr)
} } } }.
Proof.
intro H.
simpl ev2v in H.
destruct (exp_val_dec e) as [ [u Hu] | e_not_val ] ; [ left | right ].
1:{ subst. inversion H ; subst. eexists ; crush. }
destruct (sss_det (eval N) t e) as [ [t'' [e'' [w' [Hsss Unique]]]] | ].
2:{ inversion H. }
destruct (ev2v N t'' e'') as [ [[[_k _t'] _e'] w''] | ] eqn:?.
2:{ inversion H. }
inversion H; subst; clear H. do 4 eexists.
repeat split ; [ exact Hsss | ].
eexists. split ; eauto.
Qed.
End section_unfold_ev2v_S_to_Some.

Lemma sss_ev2v N t e t' e' w :
sss (eval N) t e t' e' w →
ev2v (S N) t e = match ev2v N t' e' with
                 | Some (n, t'', v, w') => Some (S n, t'', v, w * w')
                 | None => None
                 end.
Proof.
intro Hsss.
simpl ev2v.
destruct (exp_val_dec e) as [ [v Hv] | ].
1: { subst ; inversion Hsss. }
destruct (sss_det (eval N) t e) as [[_t'[_e'[_w[_Hsss Unique]]]] | H ].
2: { exfalso ; apply H ; repeat eexists ; apply Hsss. }
apply Unique in Hsss ; destruct Hsss as [? []] ; subst.
repeat match goal with
| [ |- context[ match ?x with _ => _ end ] ] => destruct x
end ; reflexivity.
Qed.

Lemma ev2v_index_bounded N : ∀ t e k t' v w,
ev2v N t e = Some (k, t', v, w) →
k <= N.
Proof.
induction N as [|N IHN]; do 6 intro; intro H.
+ simpl in H.
  destruct (exp_val_dec e) as [ [u Hu] | ]; inversion H; subst. omega.
+ simpl in H.
  destruct (exp_val_dec e) as [ [u Hu] | ]; inversion H; subst. 1:{ omega. }
  destruct (sss_det (eval N) t e) as [[_t'[_e'[_w[_Hsss Unique]]]] | Q ].
  2:{ inversion H. }
  destruct (ev2v N _ _) as [ [[[? ?] ?] ?] | ] eqn:Q; inversion H; subst.
  apply IHN in Q. omega.
Qed.

Lemma ev2v_Some_eval N t e k t' (v : val0) w :
ev2v N t e = Some (k, t', v, w) →
eval N t e = Some (t', (exp_val v), w).
Proof.
generalize t e k t' v w; clear- N. induction N as [|N IHN]; do 6 intro; intro H.
1:{
  cbn in H |- *.
  destruct (exp_val_dec e) as [[u Hu]|Nonval_e].
  + subst. inversion H. subst. reflexivity.
  + inversion H.
}
simpl in H |- *.
destruct (exp_val_dec e) as [[u Hu]|Nonval_e].
1:{ subst. inversion H. subst. reflexivity. }
destruct (exp_ktx_exn_dec e) as [[K ?]|].
1:{
  subst. exfalso.
  destruct (sss_det (eval N) t (ktx_plug K exp_exn)) as [ [t2 [e2 [w2 [Step_e_N ?]]]] |Stop_e_N].
  2:{ inversion H. }
  apply sss_ktx_exn_inv in Step_e_N. trivial.
}
destruct (sss_det (eval N) t e) as [ [t2 [e2 [w2 [Step_e_N ?]]]] |Stop_e_N].
2:{ inversion H. }
destruct (ev2v N t2 e2) as [[[[? ?] ?] ?] |] eqn:?.
2:{ inversion H. }
inversion H; subst.
erewrite IHN. 1:{ reflexivity. }
eassumption.
Qed.

Lemma ev2v_None_eval N t e :
ev2v N t e = None →
eval N t e = None ∨
∃ t' e' w, eval N t e = Some (t', e', w) ∧ (∀ v, e' = exp_val v → False).
Proof.
generalize t e; clear- N. induction N as [|N IHN]; do 2 intro; intro H.
1:{
  cbn in H |- *.
  destruct (exp_val_dec e) as [[u Hu]|Nonval_e].
  + subst. inversion H.
  + right. repeat eexists. assumption.
}
cbn in H |- *.
destruct (exp_val_dec e) as [[u Hu]|Nonval_e].
1:{ subst. inversion H. }
destruct (exp_ktx_exn_dec e) as [[K ?]|?].
1:{
  subst.
  destruct (sss_det (eval N) t (ktx_plug K exp_exn)) as [ [t2 [e2 [w2 [Step_e_N ?]]]] |Stop_e_N].
  1:{ exfalso. apply sss_ktx_exn_inv in Step_e_N. trivial. }
  right. repeat eexists. apply Nonval_e.
}
destruct (sss_det (eval N) t e) as [ [t2 [e2 [w2 [Step_e_N ?]]]] |Stop_e_N].
2:{ left. reflexivity. }
destruct (ev2v N t2 e2) as [[[[? ?] ?] ?] |] eqn:Q.
1:{ inversion H. }
apply IHN in Q as [Q | [? [? [? [Q ?]]]]].
+ rewrite Q. left; reflexivity.
+ rewrite Q. right. repeat eexists. assumption.
Qed.

Lemma eval_Some_ev2v N t e t' (v : val0) w :
eval N t e = Some (t', (exp_val v), w) →
∃ k, ev2v N t e = Some (k, t', v, w).
Proof.
generalize t e t' v w; clear- N. induction N as [|N IHN]; do 5 intro; intro H.
1:{
  cbn in H |- *.
  destruct (exp_val_dec e) as [[u Hu]|Nonval_e].
  + subst. inversion H. subst. eexists. reflexivity.
  + exfalso. inversion H. subst. eapply Nonval_e; eauto.
}
simpl in H |- *.
destruct (exp_val_dec e) as [[u Hu]|Nonval_e].
1:{ subst. inversion H. subst. eexists; reflexivity. }
destruct (exp_ktx_exn_dec e) as [[K ?]|?].
1:{ subst. inversion H; subst. ktx_plug_is_val_absurd. }
destruct (sss_det (eval N) t e) as [ [t2 [e2 [w2 [Step_e_N ?]]]] |Stop_e_N].
2:{ inversion H. }
destruct (eval N t2 e2) as [[[? ?] ?] |] eqn:Heval.
2:{ inversion H. }
inversion H; subst.
apply IHN in Heval as [? Hev2v].
eexists. rewrite Hev2v. reflexivity.
Qed.

Lemma ev2v_stuck N t e :
stop N e →
(∀ v, e = exp_val v → False) →
ev2v (S N) t e = None.
Proof.
intros Stop_e_N Nonval_e.
cbn.
destruct (exp_val_dec e) as [ [v Hv] | ].
1:{ subst; exfalso. eapply Nonval_e. reflexivity. }
destruct (sss_det (eval N) t e) as [ [?[?[?[? ?]]]] |]; [| reflexivity ].
exfalso.
destruct Stop_e_N as [Sss_False Exn_False].
specialize (Sss_False t).
eapply Sss_False.
eassumption.
Qed.

Lemma ev2v_ktx_exn N t K :
ev2v N t (ktx_plug K exp_exn) = None.
Proof.
induction N.
+ simpl. destruct (exp_val_dec _) as [[? ?]|]. 2:{ reflexivity. }
  ktx_plug_is_val_absurd.
+ simpl.
  destruct (exp_val_dec (ktx_plug K exp_exn)) as [ [v Hv] | H' ].
  1:{ ktx_plug_is_val_absurd. }
  clear H'.
  destruct (exp_ktx_exn_dec (ktx_plug K exp_exn)) as [ [J ?] | H'' ].
  2:{ exfalso. eapply H''. reflexivity. }
  destruct (sss_det (eval N) t (ktx_plug K exp_exn)) as
  [[t'[e'[w[Hsss Unique]]]] | H ].
  2:{ reflexivity. }
  exfalso. apply sss_ktx_exn_inv in Hsss. apply Hsss.
Qed.

(** The unnormalized density of termination to a value within [N] steps *)
Definition ρTV (N : nat) (t : entropy) (e : exp0) V : R⁺ :=
match eval N t e with
| Some (_, exp_val v, w) => indicator V v * w
| _ => 0
end.

(** The unnormalized density of nontermination within [N] steps *)
Definition ρNT (N : nat) (t : entropy) (e : exp0) (V : Event val0) : R⁺ :=
match eval N t e with
| Some (_, exp_val v, w) => if V v then 0 else w
| Some (_, _, w) => w
| None => 0
end.

Lemma ρTV_exn N t K V : 0 = ρTV N t (ktx_plug K exp_exn) V.
Proof.
unfold ρTV. rewrite eval_ktx_exn.
destruct (ktx_plug K exp_exn) eqn:?; try ring.
exfalso. ktx_plug_is_val_absurd.
Qed.

Lemma ρNT_exn N t K V : 1 = ρNT N t (ktx_plug K exp_exn) V.
Proof.
unfold ρNT. rewrite eval_ktx_exn.
destruct (ktx_plug K exp_exn) eqn:?; try ring.
ktx_plug_is_val_absurd.
Qed.

Lemma ev2v_ρTV_same_weight N t e (V : Event val0) :
match ev2v N t e with
| Some (_, _, v, w) => if V v then w else 0
| None => 0
end = ρTV N t e V.
Proof.
generalize t e; clear t e.
induction N as [ | N IHN ]; intros t e.
1:{
  cbn. unfold indicator, ifte.
  destruct (exp_val_dec e) as [[v Hv]|Nonval_e] eqn: Dec_val_e.
  + subst; ring.
  + destruct e; try ring; try inversion Dec_val_e.
}
destruct (exp_val_dec e) as [[v Hv]|Nonval_e] eqn: Dec_val_e.
1:{ subst. unfold ρTV, indicator, ifte. simpl. ring. }
destruct (exp_ktx_exn_dec e) as [[K ?]|Nonexn_e] eqn: Dec_exn_e.
1:{ subst. rewrite ev2v_ktx_exn. erewrite <-ρTV_exn. ring. }
destruct (sss_det (eval N) t e) as [ [t' [e' [w [Step_e_N ?]]]] |Stop_e_N] eqn: Det_sss.
+ simpl ev2v. unfold ρTV. simpl eval.
  rewrite Dec_val_e, Dec_exn_e, Det_sss. clear Det_sss.
  specialize (IHN t' e').
  destruct (ev2v N t' e') as [[[[k t''] v] w']|] eqn:Ev2v.
  2:{
    unfold ρTV in IHN.
    destruct (eval N t' e') as [[[t'' e''] w'']|]; [|ring].
    destruct e'' as [u| | | | | | | |]; try ring.
    unfold indicator, ifte in IHN |- *.
    apply eq_sym in IHN. apply ennr_mult_integral in IHN.
    destruct IHN as [IHN|IHN].
    + rewrite IHN. ring.
    + rewrite IHN. ring.
  }
  destruct (V v) eqn:Q.
  - subst w'. unfold ρTV.
    destruct (eval N t' e') as [[[t''_ e''_] w''_]|]; [|ring].
    unfold indicator. simpl ifte.
    destruct e''_; ring.
  - destruct (eval N t' e') as [[[t''_ e''_] w''_]|] eqn:H; [|ring].
    destruct e''_; try ring.
    apply eval_Some_ev2v in H as [? H]. rewrite H in Ev2v.
    inversion Ev2v. subst. unfold indicator, ifte. rewrite Q. ring.
+ simpl ev2v. unfold ρTV. simpl eval.
  rewrite Dec_val_e, Dec_exn_e, Det_sss. ring.
Qed.

Hint Extern 1 => match goal with
| [ |- (0 ≤ ?r)%ennr ] => apply ennr_le_0
| [ |- (?r ≤ ∞)%ennr ] => apply ennr_le_infinity
| [ |- (?r ≤ ?r)%ennr ] => apply ennr_le_refl
end : core.

Lemma sss_quadfurcate N t e t' e' w :
(eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w → (
  (∀ _N _t, (eval _N) ⟨_t|e⟩ ⤳ ⟨_t|e'⟩ • w ) ∧ w ≤ 1
) ∨ (
  ∃ K f,
  t = t' ∧
  0 < μNS N f ∧
  e = K[/(exp_sample (val_query f))] ∧
  e' = K[/f] ∧
  w = / μNS N f
) ∨ (
  ∃ K f,
  t = t' ∧
  0 = μNS N f ∧
  e = K[/(exp_sample (val_query f))] ∧
  e' = K[/exp_exn] ∧
  w = 1
) ∨ (
  ∃ K,
  t' = πR t ∧
  e =  K[/(exp_sample val_unif)] ∧
  e' =  K[/(val_real (proj1_sig (πL t 0%nat)))] ∧
  w = 1
).
Proof.
induction 1.
+ left; clear N t; split; [intros N t; constructor; auto|auto].
+ left; clear N t; split; [intros N t; constructor; auto|auto].
+ left; clear N t; split; [intros N t; constructor; auto|auto].
+ left; clear N t; split; [intros N t; constructor; auto|auto].
+ left; clear N t; split; [intros N t; constructor; auto|auto].
+ left; clear N t; split; [intros N t; constructor; auto|auto].
+ left; clear N t; split; [intros N t; constructor; auto|auto].
+ right; right; right. exists ktx_hole ; crush.
+ right; left.
  exists ktx_hole; eexists.
  repeat split; try eassumption.
+ right; right; left.
  exists ktx_hole; eexists.
  repeat split; try eassumption.
+ left; clear N t; split; [intros N t; constructor; auto|].
  match goal with [ H: (r ≤ 1)%R |- _ ] => destruct H end.
  - left. simpl. assumption.
  - right. subst. Finite.
+ destruct IHsss as [ Q | [ Q | [ Q | Q ] ] ]; [ left | right; left | right; right ; left | right ; right ; right ].
  - clear- Q. destruct Q. 
    split; [intros N t; apply sss_ktx_app1; eauto|assumption].
  - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
    eexists (ktx_app1 K _); repeat eexists; auto.
  - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
    eexists (ktx_app1 K _); repeat eexists; auto.
  - clear- Q. destruct Q as [K [? [? [? ?]]]]; subst.
    eexists (ktx_app1 K _); repeat eexists.
+ destruct IHsss as [ Q | [ Q | [ Q | Q ] ] ]; [ left | right; left | right; right ; left | right ; right ; right ].
  - clear- Q. destruct Q.
    split; [intros N t; apply sss_ktx_app2; eauto|eassumption].
  - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
    eexists (ktx_app2 _ K); repeat eexists; auto.
  - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
    eexists (ktx_app2 _ K); repeat eexists; auto.
  - clear- Q. destruct Q as [K [? [? [? ?]]]]; subst.
    eexists (ktx_app2 _ K); repeat eexists.
+ destruct IHsss as [ Q | [ Q | [ Q | Q ] ] ]; [ left | right; left | right; right ; left | right ; right ; right ].
    - clear- Q. destruct Q.
      split; [intros N t; apply sss_ktx_let; eauto|assumption].
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_let K _); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_let K _); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? ?]]]]; subst.
      eexists (ktx_let K _); repeat eexists.
+ destruct IHsss as [ Q | [ Q | [ Q | Q ] ] ]; [ left | right; left | right; right ; left | right ; right ; right ].
  - clear- Q. destruct Q.
    split; [intros N t; apply sss_ktx_binop1; eauto|assumption].
  - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
    eexists (ktx_binop1 _ K _); repeat eexists; auto.
  - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
    eexists (ktx_binop1 _ K _); repeat eexists; auto.
  - clear- Q. destruct Q as [K [? [? [? ?]]]]; subst.
    eexists (ktx_binop1 _ K _); repeat eexists.
+ destruct IHsss as [ Q | [ Q | [ Q | Q ] ] ]; [ left | right; left | right; right ; left | right ; right ; right ].
    - clear- Q. destruct Q.
      split; [intros N t; apply sss_ktx_binop2; eauto|assumption].
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_binop2 _ _ K); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_binop2 _ _ K); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? ?]]]]; subst.
      eexists (ktx_binop2 _ _ K); repeat eexists.
+ destruct IHsss as [ Q | [ Q | [ Q | Q ] ] ]; [ left | right; left | right; right ; left | right ; right ; right ].
  - clear- Q. destruct Q.
    split; [intros N t; apply sss_ktx_proj; eauto|assumption].
  - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
    eexists (ktx_proj K _); repeat eexists; auto.
  - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
    eexists (ktx_proj K _); repeat eexists; auto.
  - clear- Q. destruct Q as [K [? [? [? ?]]]]; subst.
    eexists (ktx_proj K _); repeat eexists.
+ destruct IHsss as [ Q | [ Q | [ Q | Q ] ] ]; [ left | right; left | right; right ; left | right ; right ; right ].
    - clear- Q. destruct Q.
      split; [intros N t; apply sss_ktx_if; eauto|assumption].
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_if K _ _); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_if K _ _); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? ?]]]]; subst.
      eexists (ktx_if K _ _); repeat eexists.
+ destruct IHsss as [ Q | [ Q | [ Q | Q ] ] ]; [ left | right; left | right; right ; left | right ; right ; right ].
    - clear- Q. destruct Q.
      split; [intros N t; apply sss_ktx_sample; eauto|assumption].
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_sample K); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_sample K); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? ?]]]]; subst.
      eexists (ktx_sample K); repeat eexists.
+ destruct IHsss as [ Q | [ Q | [ Q | Q ] ] ]; [ left | right; left | right; right ; left | right ; right ; right ].
    - clear- Q. destruct Q.
      split; [intros N t; apply sss_ktx_score; eauto|assumption].
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_score K); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? [? [? ?]]]]]]; subst.
      eexists (ktx_score K); repeat eexists; auto.
    - clear- Q. destruct Q as [K [? [? [? ?]]]]; subst.
      eexists (ktx_score K); repeat eexists.
Qed.

Ltac solve_pt := repeat match goal with
| [ H : wf_exp _ (exp_val _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_exp _ (exp_app _ _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_exp _ (exp_let _ _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_exp _ (exp_binop _ _ _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_exp _ (exp_proj _ _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_exp _ (exp_if _ _ _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_exp _ (exp_sample _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_exp _ (exp_score _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_val _ (val_var _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_val _ (val_fun _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_val _ (val_fix _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_val _ val_unif _ |- _ ] => inversion H; clear H; subst
| [ H : wf_val _ (val_pair _ _) _ |- _ ] => inversion H; clear H; subst
| [ H : wf_val _ (val_query _) _ |- _ ] => inversion H; clear H; subst
end.

Section section_sss_preserves_type.

Hint Constructors wf_exp wf_val : core.

Lemma sss_preserves_type :
∀ N t e t' e' w, (eval N) ⟨t|e⟩ ⤳ ⟨t'|e'⟩ • w  → ∀ T, wf_exp ∅→ e T → wf_exp ∅→ e' T.
Proof.
induction 1; simpl; intros T Wf_e.
+ solve_pt. eapply V_bind_wf_exp. 1:{ eassumption. }
  intro x; destruct x as [|x]; simpl; auto.
+ solve_pt. eapply V_bind_wf_exp. 1:{ eassumption. }
  intro x; destruct x as [|x]; simpl; auto.
+ solve_pt. eapply V_bind_wf_exp. 1:{ eassumption. }
  intro x; destruct x as [|x]; simpl; auto.
+ solve_pt. destruct v1, v2; simpl in H; try inversion H.
  destruct op; simpl in H|-*; auto.
+ solve_pt. destruct b; auto.
+ solve_pt. auto.
+ solve_pt. auto.
+ solve_pt. auto.
+ solve_pt. auto.
+ auto.
+ solve_pt. auto.
+ solve_pt. eauto.
+ solve_pt. eauto.
+ solve_pt. eauto.
+ solve_pt. eauto.
+ solve_pt. eauto.
+ solve_pt. eauto.
+ constructor. eapply IHsss; inversion Wf_e; eauto.
  inversion Wf_e. auto. inversion Wf_e; eauto.
+ solve_pt. eauto.
+ solve_pt. eauto.
Qed.

End section_sss_preserves_type.
Lemma ev2v_preserves_type N : ∀ t e k t' v w T,
ev2v N t e = Some (k, t', v, w) →
wf_exp ∅→ e T →
wf_val ∅→ v T.
Proof.
induction N as [|N IHN]; do 7 intro; intros Ev_e Wf_e.
1:{
  simpl in Ev_e. destruct (exp_val_dec e) as [[u Hu] | NV_e].
  + inversion Ev_e. subst. inversion Wf_e; assumption.
  + inversion Ev_e.
}
simpl in Ev_e.
destruct (exp_val_dec e) as [[u Hu] | NV_e].
1:{ inversion Ev_e. subst. inversion Wf_e; assumption. }
destruct (sss_det (eval N) t e) as [ [t'' [e'' [w' [Hsss Unique]]]] | ].
2:{ inversion Ev_e. }
destruct (ev2v N t'' e'') as [[[[? ?] ?] ?] |] eqn:Q.
2:{ inversion Ev_e. }
inversion Ev_e. subst.
eapply IHN. 1:{ apply Q. }
eapply sss_preserves_type. 1:{ apply Hsss. } 1:{ apply Wf_e. }
Qed.
Arguments ev2v_preserves_type [N t e k t' v w T].
