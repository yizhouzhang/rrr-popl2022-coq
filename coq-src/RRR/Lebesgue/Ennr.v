(** This file defines the extended non-negative real type [ennr] representing
a number in the interval #[0, ∞]#. We will define integrals to be over [ennr]
as we are only interested in integrating measures and markov kernels.

This file lifts several useful definitions and theorems from [R], and proves
that [ennr] forms a semiring so that the [ring] tactic will apply.

Some lemmas are left admitted, but they should be straightforward to prove.
*)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Program.Basics.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Minus.

Require Import RRR.Util.Option.

Declare Scope ennr_scope.
Delimit Scope ennr_scope with ennr.
Local Open Scope R.
Local Open Scope ennr_scope.

Export RingSyntax.

Require Export Coq.Reals.Reals.

Infix "≤" := Rle : R_scope.
Infix "≥" := Rge : R_scope.
Notation "r1 ≤ r2 ≤ r3" := (r1 ≤ r2 ∧ r2 ≤ r3) (at level 70, r2 at next level) : R_scope.

Inductive ennr :=
| finite (r : R) (r_pos : 0 ≤ r)
| infinite.
Notation "R⁺" := ennr : ennr_scope.
Notation "∞" := infinite : ennr_scope.

(** * Equality *)

(** Equality between finite [ennr]s is shown to be exactly equality on [R]
through the genererous help of [proof_irrelevance]. It would probably be
possible to prove the important results without relying on proof
irrelevance, but it simplifies things greatly here. *)
Lemma finite_inj r0 r0_pos r1 r1_pos :
r0 = r1 →
finite r0 r0_pos = finite r1 r1_pos.
Proof.
intros.
subst.
f_equal.
apply proof_irrelevance.
Qed.
Hint Immediate finite_inj : core.
Ltac Finite := apply finite_inj; try solve [cbn; ring].

(** * [ennr] is a semiring *)
Program Definition ennr_0 := finite 0 (Rle_refl _).
Program Definition ennr_1 := finite 1 (Rlt_le 0 1 Rlt_0_1).
Notation "0" := ennr_0 : ennr_scope.
Notation "1" := ennr_1 : ennr_scope.

Definition option0 : option R⁺ → R⁺ := fromOption 0.

Definition ennr_plus (a b : R⁺) : R⁺ :=
match a, b with
| finite ra ra_pos, finite rb rb_pos
  => finite (ra + rb) (Rplus_le_le_0_compat _ _ ra_pos rb_pos)
| _, _ => ∞
end.
Infix "+" := ennr_plus : ennr_scope.

Parameter ennr_minus : ∀ (a b : R⁺), R⁺.
Infix "-" := ennr_minus : ennr_scope.

Definition ennr_mult (a b : R⁺) : R⁺ :=
match a, b with
| finite ra ra_pos, finite rb rb_pos
  => finite (ra * rb) (Rmult_le_pos _ _ ra_pos rb_pos)
| finite ra ra_pos, ∞
  => if Req_EM_T 0 ra then 0 else ∞
| ∞, finite rb rb_pos
  => if Req_EM_T 0 rb then 0 else ∞
| ∞, ∞
  => ∞
end.
Infix "*" := ennr_mult : ennr_scope.

Lemma ennr_add_0_l : ∀ n, 0 + n = n.
Proof.
destruct n; auto; Finite.
Qed.

Axiom ennr_minus_0 : ∀ r, r - 0 = r.
Axiom ennr_minus_self : ∀ r, r - r = 0.

Lemma ennr_add_comm : ∀ n m, n + m = m + n.
Proof.
destruct n, m; auto; Finite.
Qed.

Lemma ennr_add_assoc : ∀ n m p, n + (m + p) = (n + m) + p.
Proof.
destruct n, m, p; auto; Finite.
Qed.

Lemma ennr_mul_1_l : ∀ n, 1 * n = n.
Proof.
destruct n; simpl; auto.
- Finite.
- destruct Req_EM_T; simpl; auto.
  lra.
Qed.

Local Hint Extern 1 => match goal with
| [ H : ?r ≠ ?r |- _ ] => contradict H ; reflexivity
end : core.

Lemma ennr_mul_0_l : ∀ n, 0 * n = 0.
Proof.
destruct n; simpl; auto.
- Finite.
- destruct Req_EM_T; simpl; auto.
Qed.

Lemma ennr_mul_comm : ∀ n m, n * m = m * n.
Proof.
destruct n, m; auto; Finite.
Qed.

Lemma ennr_mul_assoc : ∀ n m p, n * (m * p) = (n * m) * p.
Proof.
assert (∀ r0 r1, 0 = r0 * r1 → 0 ≠ r0 → 0 ≠ r1 → False)%R.
+ intros.
  contradict H0.
  replace r0 with ((r0 * r1) * / r1)%R. {
    rewrite <- H.
    ring.
  } {
    rewrite Rmult_assoc.
    rewrite Rinv_r; auto.
    ring.
  }
+ destruct n, m, p;
  repeat (try destruct Req_EM_T; simpl);
  subst;
  auto;
  solve
    [ Finite
    | contradict n; ring
    | contradict n0; ring
    | contradict H; eauto
    ].
Qed.

Lemma ennr_distr_l : ∀ n m p, (n + m) * p = n * p + m * p.
Proof.
destruct n, m, p;
  repeat (try destruct Req_EM_T; simpl);
  subst;
  auto;
  try Finite.
+ contradict n.
  rewrite e.
  ring.
+ contradict n.
  apply Rle_antisym; auto.
  rewrite e.
  replace r with (r + 0)%R at 1 by ring.
  apply Rplus_le_compat; auto.
  apply Rle_refl.
+ contradict n; ring.
Qed.

Lemma ennr_distr_r : ∀ n m p, p * (n + m) = p * n + p * m.
Proof.
  intros.
  rewrite ennr_mul_comm.
  rewrite ennr_distr_l.
  repeat rewrite ennr_mul_comm with (m := p).
  reflexivity.
Qed.

Arguments ennr_plus _ _ : simpl never.
Arguments ennr_mult _ _ : simpl never.

Definition ennr_semiring :=
mk_srt ennr_0 ennr_1 ennr_plus ennr_mult eq
  ennr_add_0_l
  ennr_add_comm
  ennr_add_assoc
  ennr_mul_1_l
  ennr_mul_0_l
  ennr_mul_comm
  ennr_mul_assoc
  ennr_distr_l
.
Add Ring ennr_semiring : ennr_semiring.

Definition ennr_inv (a : R⁺) : R⁺.
Proof.
refine (match a with
| finite ra ra_pos =>
  if Req_EM_T ra 0
  then ∞
  else finite (/ ra) _
| ∞ => finite 0 (Rle_refl 0)
end).
destruct (Rle_lt_or_eq_dec _ _ ra_pos) as [ H | H ].
+ apply Rlt_le.
  apply Rinv_0_lt_compat.
  exact H.
+ lra.
Defined.
Notation "/ x" := (ennr_inv x) : ennr_scope.

Definition ennr_div a b := a * / b.

Lemma ennr_inv_0 : / 0 = ∞.
Proof.
cbn.
destruct (Req_EM_T 0 0) as [ H | H ] ; auto.
Qed.

Lemma ennr_inv_infinity : / ∞ = 0.
Proof.
auto.
Qed.

Lemma ennr_inv_is_zero r : 0 = / r → r = ∞.
Proof.
Admitted.

Lemma ennr_inv_1 : / 1 = 1.
Proof.
simpl.
destruct (Req_EM_T 1 0) as [ H | H ] ; auto.
+ lra.
+ apply finite_inj.
  lra.
Qed.

Lemma ennr_1_neq_0 : ~ 1 = 0.
Proof. intro C. inversion C. lra. Qed.

Lemma ennr_div_def : ∀ p q, ennr_div p q = p * / q.
Proof. reflexivity. Qed.

(** * Misc definitions and facts about [ennr]. *)

Definition ennr_lt (a b : R⁺) : Prop :=
match a, b with
| finite ra _, finite rb _ => ra < rb
| finite _ _, ∞ => True
| ∞, _ => False
end.
Definition ennr_gt a b := ennr_lt b a.
Definition ennr_le a b := ennr_lt a b ∨ a = b.
Definition ennr_ge a b := ennr_gt a b ∨ a = b.
Infix "<" := ennr_lt : ennr_scope.
Infix "≤" := ennr_le : ennr_scope.
Infix ">" := ennr_gt : ennr_scope.
Infix "≥" := ennr_ge : ennr_scope.
Notation "r1 < r2 < r3" := (r1 < r2 ∧ r2 < r3) (at level 70, r2 at next level) : ennr_scope.
Notation "r1 ≤ r2 ≤ r3" := (r1 ≤ r2 ∧ r2 ≤ r3) (at level 70, r2 at next level) : ennr_scope.
Notation "r1 < r2 ≤ r3" := (r1 < r2 ∧ r2 ≤ r3) (at level 70, r2 at next level) : ennr_scope.

Lemma ennr_0_lt_dec (r : R⁺) : {0 < r} + {0 = r}.
Proof.
destruct r; simpl.
+ destruct (Rlt_dec 0 r).
  - left. assumption.
  - right. assert (0 = r)%R.
    1:{ apply Rle_antisym; [ assumption | ]. apply Rnot_lt_le. assumption. }
    subst r. apply finite_inj. reflexivity.
+ left; auto.
Qed.

Lemma ennr_add_0_r : ∀ r, r + 0 = r.
Proof.
intro. ring.
Qed.

Lemma ennr_mul_1_r : ∀ r, r * 1 = r.
Proof.
intro. ring.
Qed.

Axiom ennr_minus_distr_l : ∀ n m p, m ≤ n → (n - m) * p = n * p - m * p.
Axiom ennr_minus_distr_r : ∀ n m p, m ≤ n → p * (n - m) = p * n - p * m.

Lemma ennr_lt_dec (a b : R⁺) : {a < b} + {¬ a < b}.
Proof.
destruct a, b; simpl; auto.
apply Rgt_dec.
Qed.

Lemma ennr_gt_dec (a b : R⁺) : {a > b} + {¬ a > b}.
Proof.
destruct a, b; simpl; auto.
apply Rgt_dec.
Qed.

Lemma ennr_le_0 (r : R⁺) : 0 ≤ r.
Proof.
Admitted.

Lemma ennr_le_0_is_0 (r : R⁺) : r ≤ 0 → 0 = r.
Proof.
Admitted.

Lemma ennr_le_refl (r : R⁺) : r ≤ r.
Proof.
right ; reflexivity.
Qed.

Lemma ennr_lt_trans (r1 r2 r3 : R⁺) :
r1 < r2 → r2 < r3 → r1 < r3.
Proof.
Admitted.

Lemma ennr_le_trans (r1 r2 r3 : R⁺) :
r1 ≤ r2 → r2 ≤ r3 → r1 ≤ r3.
Proof.
Admitted.

Lemma ennr_le_lt_trans (r1 r2 r3 : R⁺) :
r1 ≤ r2 → r2 < r3 → r1 < r3.
Proof.
Admitted.

Lemma ennr_lt_le_trans (r1 r2 r3 : R⁺) :
r1 < r2 → r2 ≤ r3 → r1 < r3.
Proof.
Admitted.

Lemma ennr_lt_irrefl r : ¬ r < r.
Admitted.

Lemma ennr_le_not_le (r1 r2 : R⁺) : r1 ≤ r2 ↔ (¬ r2 < r1).
Proof.
Admitted. 

Lemma ennr_lt_not_eq r1 r2 : r1 < r2 → r1 ≠ r2.
Proof.
Admitted.

Lemma ennr_mul_0_r r : r * 0 = 0.
Proof.
Admitted.

Lemma ennr_add_le_compat_1 r1 r2 : r1 ≤ r1 + r2.
Proof.
Admitted.

Lemma ennr_add_le_compat_2 r1 r2 : r2 ≤ r1 + r2.
Proof.
Admitted.

Lemma ennr_add_le_compat_l r r1 r2 : r1 ≤ r2 → r + r1 ≤ r + r2.
Proof.
Admitted.

Lemma ennr_add_le_compat_r r r1 r2 : r1 ≤ r2 → r1 + r ≤ r2 + r.
Proof.
Admitted.

Lemma ennr_add_le_compat r1 r2 r3 r4 : r1 ≤ r2 → r3 ≤ r4 → r1 + r3 ≤ r2 + r4.
Proof.
Admitted.

Axiom ennr_plus_minus :
∀ r1 r2 r3, r2 ≤ r1 → r1 = r2 + r3 <-> r1 - r2 = r3.

Lemma ennr_minus_le_compat_r r r1 r2 :
r1 ≤ r → r2 ≤ r → r2 ≤ r1 → r - r1 ≤ r - r2.
Proof.
Admitted.

Lemma ennr_minus_le_compat r1 r1' r2 r2' :
r1 ≤ r1' → r2 ≤ r2' → r2 ≤ r1 → r1' ≤ r2' → r1' - r1 ≤ r2' - r2.
Proof.
Admitted.

Lemma ennr_inv_involutive r : / / r = r.
Proof.
Admitted.

Lemma ennr_inv_0_lt_compat r : 0 < r → / r < ∞.
Proof.
Admitted.

Lemma ennr_inv_finite_compat r : r < ∞ → 0 < / r.
Proof.
Admitted.

Lemma ennr_inv_0_lt_finite_compat r : 0 < r → r < ∞ → 0 < / r < ∞.
Proof.
Admitted.

Lemma ennr_mult_0_lt_compat r1 r2 : 0 < r1 * r2 ↔ 0 < r1 ∧ 0 < r2.
Proof.
Admitted.

Lemma ennr_mult_le_compat_l r r1 r2 : r1 ≤ r2 → r * r1 ≤ r * r2.
Proof.
Admitted.

Lemma ennr_mult_le_compat_r r r1 r2 : r1 ≤ r2 → r1 * r ≤ r2 * r.
Proof.
Admitted.

Lemma ennr_mult_le_compat r1 r2 r3 r4 : r1 ≤ r2 → r3 ≤ r4 → r1 * r3 ≤ r2 * r4.
Proof.
Admitted.

Lemma ennr_mult_le_1_compat r1 r2 : r1 ≤ 1 → r2 ≤ 1 → r1 * r2 ≤ 1.
Proof.
Admitted.

Lemma ennr_add_eq_compat_r r r1 r2 : r1 = r2 <-> r1 + r = r2 + r.
Proof.
Admitted.

Lemma ennr_mult_eq_compat_l r r1 r2 : r1 = r2 → r * r1 = r * r2.
Proof.
Admitted.

Lemma ennr_mult_integral r1 r2 : r1 * r2 = 0 → r1 = 0 ∨ r2 = 0.
Proof.
Admitted.

Lemma ennr_le_antisym r1 r2 : r1 ≤ r2 → r2 ≤ r1 → r1 = r2.
Proof.
Admitted.

Lemma ennr_le_infinity r : r ≤ ∞.
Proof.
Admitted.

Lemma ennr_mult_r_pos_lt_infinity_inv r1 r2 : r1 * r2 < ∞ → 0 < r2 → r1 < ∞.
Proof.
Admitted.

Lemma ennr_mul_infinity_l r : 0 < r → ∞ * r = ∞.
Proof.
Admitted.

Lemma ennr_mul_infinity_r r : 0 < r → r * ∞ = ∞.
Proof.
rewrite ennr_mul_comm.
apply ennr_mul_infinity_l.
Qed.

Lemma ennr_mult_inv_r_finite r : 0 < r → r < ∞ → r * / r = 1.
Proof.
Admitted.

Lemma ennr_mult_inv_l_finite r : 0 < r → r < ∞ → (/ r) * r = 1.
Proof.
Admitted.

Lemma ennr_mult_inv_r_le_1 r : r * / r ≤ 1.
Proof.
Admitted.

Lemma ennr_mult_inv_le_compat r1 r2 : r2 ≤ r1 → / r1 ≤ / r2.
Proof.
Admitted.

Lemma ennr_mult_inv_le_1_compat r1 r2 : r1 ≤ r2 → r1 * / r2 ≤ 1.
Proof.
Admitted.

Lemma ennr_mult_0_lt r1 r2 : 0 < r1 → 0 < r2 → 0 < r1 * r2.
Proof.
destruct r1 as [r1 r1_pos|], r2 as [r2 r2_pos|]; simpl; intros Hr1 Hr2.
+ prove_sup; lra.
+ rewrite ennr_mul_infinity_r; auto.
+ rewrite ennr_mul_infinity_l; auto.
+ trivial. 
Qed.

Lemma ennr_mult_finite r1 r2 : r1 < ∞ → r2 < ∞ → r1 * r2 < ∞.
Proof.
destruct r1 as [r1 r1_pos|], r2 as [r2 r2_pos|]; simpl; intros Hr1 Hr2.
+ trivial.
+ exfalso; trivial.
+ exfalso; trivial.
+ trivial.
Qed.

Lemma ennr_mult_0_lt_and_finite r1 r2 :
0 < r1 < ∞ → 0 < r2 < ∞ → 0 < r1 * r2 < ∞.
Proof.
intros Hr1 Hr2.
destruct Hr1, Hr2.
split.
+ apply ennr_mult_0_lt; assumption.
+ apply ennr_mult_finite; assumption.
Qed.

Lemma ennr_0_lt_compat_mult_infinity r1 r2 :
(0 < r1 → 0 < r2) → r1 ≤ ∞ * r2.
Proof.
Admitted.

Lemma ennr_mult_infinity_compat_0_lt r1 r2 :
r1 ≤ ∞ * r2 → 0 < r1 → 0 < r2.
Proof.
intros H H1.
destruct (ennr_0_lt_dec r1) as [|Q].
+ destruct (ennr_0_lt_dec r2) as [H2|H2].
  - trivial.
  - exfalso.
    rewrite <- H2, ennr_mul_comm, ennr_mul_0_l in H.
    assert (0 = r1) as P.
    1:{ eapply ennr_le_antisym ; [ apply ennr_le_0 | apply H ]. }
    rewrite <- P in H1.
    apply ennr_lt_irrefl in H1 ; trivial.
+ exfalso.
  rewrite <- Q in H1.
  apply ennr_lt_irrefl in H1 ; trivial.
Qed.

Lemma ennr_0_eq_compat_mult_infinity r1 r2 :
(0 = r2 → 0 = r1) → r1 ≤ ∞ * r2.
Proof.
Admitted.

Lemma ennr_mult_infinity_compat_0_eq r1 r2 :
r1 ≤ ∞ * r2 → 0 = r2 → 0 = r1.
Proof.
Admitted.

Lemma ennr_inv_lt_infinity r :
0 < r → / r < ∞.
Proof.
Admitted.

Lemma ennr_inv_mult_distr_finite r1 r2 :
r1 < ∞ → r2 < ∞ → / (r1 * r2) = / r1 * / r2.
Proof.
Admitted.

Fact ennr_inv_useful_fact (A B A' B' c c' : R⁺) :
A' ≤ B' → A ≤ B →
B - A ≤ B' - A' →
B' + c' ≤ B + c →
B + c < ∞ →
(A' + c') * / (B' + c') ≤ (A + c) * / (B + c).
Proof.
Admitted.

Lemma Rinterval_dec r1 r2 r : ({r1 ≤ r ≤ r2} + {¬ r1 ≤ r ≤ r2})%R.
Proof.
Admitted.

Lemma Rinterval_dec' r1 r2 r: ({r1 < r ≤ r2} + {¬ r1 < r ≤ r2})%R.
Proof.
Admitted.

Definition is_upper_bound (E: R⁺ → Prop) r' := ∀ r, E r → r ≤ r'.
Definition is_lub (E: R⁺ → Prop) r' :=
is_upper_bound E r' ∧ (∀ r, is_upper_bound E r → r' ≤ r).
Definition is_lower_bound (E: R⁺ → Prop) r' := ∀ r, E r → r' ≤ r.
Definition is_glb (E: R⁺ → Prop) r' :=
is_lower_bound E r' ∧ (∀ r, is_lower_bound E r → r ≤ r').

Parameter sup : ∀ f : nat → R⁺, R⁺.
Axiom sup_is_lub : ∀ f, is_lub (λ r, ∃ n, r = f n) (sup f).
Parameter inf : ∀ f : nat → R⁺, R⁺.
Axiom inf_is_glb : ∀ f, is_glb (λ r, ∃ n, r = f n) (inf f).

Parameter has_lim : ∀ f : nat → R⁺, Prop.
Parameter lim : ∀ f : nat → R⁺, has_lim f → R⁺.

Definition monotone (f : nat → R⁺) : Prop :=
∀ N' N, (N' <= N)%nat → f N' ≤ f N.
Definition antitone (f : nat → R⁺) : Prop :=
∀ N' N, (N' <= N)%nat → f N ≤ f N'.

Lemma antitone_add_compat : ∀ f g,
antitone f → antitone g →
antitone (λ n : nat, f n + g n).
Proof.
  unfold antitone. intros.
  eapply ennr_add_le_compat; auto.
Qed.

Lemma antitone_mult_l : ∀ c f,
antitone f → antitone (λ n : nat, c * f n).
Proof.
  unfold antitone. intros.
  eapply ennr_mult_le_compat_l.
  auto.
Qed.

Lemma monotone_add_compat : ∀ f g,
monotone f → monotone g →
monotone (λ n : nat, f n + g n).
Proof.
  unfold monotone. intros.
  eapply ennr_add_le_compat; auto.
Qed.

Lemma monotone_mult_l : ∀ c f,
monotone f → monotone (λ n : nat, c * f n).
Proof.
  unfold monotone. intros.
  eapply ennr_mult_le_compat_l.
  auto.
Qed.

Ltac monotone :=
  match goal with
  | [|- antitone (λ n : nat, _ + _)] => apply antitone_add_compat
  | [|- antitone (λ n : nat, _ * _)] => apply antitone_mult_l
  | [|- monotone (λ n : nat, _ + _)] => apply monotone_add_compat
  | [|- monotone (λ n : nat, _ * _)] => apply monotone_mult_l
  | [|- _] => idtac
  end.

Axiom sup_S :
∀ (f : nat → R⁺), f O ≤ f (S O) → sup f = sup (λ n, f (S n)).
Axiom inf_S :
∀ (f : nat → R⁺), f (S O) ≤ f O → inf f = inf (λ n, f (S n)).

Axiom sup_monotone :
∀ (f : nat → R⁺), monotone f → ∀ k, sup f = sup (λ n, f (n + k)%nat).
Axiom inf_antitone :
∀ (f : nat → R⁺), antitone f → ∀ k, inf f = inf (λ n, f (n + k)%nat).

Axiom sup_extensionality :
∀ (f g : nat → R⁺), (∀ n, f n = g n) → sup f = sup g.
Axiom inf_extensionality :
∀ (f g : nat → R⁺), (∀ n, f n = g n) → inf f = inf g.

Axiom sup_of_constant :
∀ (f : nat → R⁺) (r : R⁺), (∀ n, f n = r) →
sup f = r.

Axiom inf_of_constant :
∀ (f : nat → R⁺) (r : R⁺), (∀ n, f n = r) →
inf f = r.

Axiom sup_of_constant_minus :
∀ (f : nat → R⁺) (r : R⁺),
sup (λ n, r - f n) = r - inf f.

Axiom sup_of_constant_plus :
∀ (f : nat → R⁺) (r : R⁺),
sup (λ n, r + f n) = r + sup f.

Axiom sup_linear_mult_r :
∀ (f : nat → R⁺) (r : R⁺), (r = ∞ → 0 < sup f) →
sup (λ n, f n * r) = sup f * r.

Axiom sup_linear_mult_l :
∀ (f : nat → R⁺) (r : R⁺), (r = ∞ → 0 < sup f) →
sup (λ n, r * f n) = r * sup f.

Axiom inf_linear_mult_r :
∀ (f : nat → R⁺) (r : R⁺), (0 = r → inf f < ∞) →
inf (λ n, f n * r) = inf f * r.

Axiom inf_linear_mult_l :
∀ (f : nat → R⁺) (r : R⁺), (r = ∞ → 0 < inf f) →
inf (λ n, r * f n) = r * inf f.

Axiom monotone_has_lim :
∀ (f : nat → R⁺), monotone f → has_lim f.

Axiom antitone_has_lim :
∀ (f : nat → R⁺), antitone f → has_lim f.

Axiom diff_has_lim :
∀ (f g : nat → R⁺), (∀ n, g n ≤ f n) →
has_lim f → has_lim g → has_lim (λ n, f n - g n).

Axiom sum_has_lim :
∀ (f g : nat → R⁺),
has_lim f → has_lim g → has_lim (λ n, f n + g n).

Axiom prod_has_lim :
∀ (f g : nat → R⁺),
has_lim f → has_lim g → has_lim (λ n, f n * g n).

Axiom inv_has_lim :
∀ (f : nat → R⁺), has_lim f → has_lim (λ n, / f n).

Axiom sup_is_lim :
∀ (f : nat → R⁺) (P : monotone f),
sup f = lim f (monotone_has_lim f P).

Axiom sup_is_lim' :
∀ (f : nat → R⁺) (P : monotone f) (H : has_lim f),
sup f = lim f H.

Axiom inf_is_lim :
∀ (f : nat → R⁺) (P : antitone f),
inf f = lim f (antitone_has_lim f P).

Axiom inf_is_lim' :
∀ (f : nat → R⁺) (P : antitone f) (H : has_lim f),
inf f = lim f H.

Axiom lim_of_sum :
∀ (f g : nat → R⁺) (Hf : has_lim f) (Hg : has_lim g)
  (Hsum : has_lim (λ n, f n + g n)),
lim (λ n, f n + g n) Hsum = lim f Hf + lim g Hg.

Axiom lim_of_difference :
∀ (f g : nat → R⁺) (_ : ∀ n, g n ≤ f n) (Hf : has_lim f) (Hg : has_lim g)
  (Hdiff : has_lim (λ n, f n - g n)),
lim (λ n, f n - g n) Hdiff = lim f Hf - lim g Hg.

Axiom lim_of_product :
∀ (f g : nat → R⁺) (Hf : has_lim f) (Hg : has_lim g)
  (Hprod : has_lim (λ n, f n * g n)),
(0 = lim f Hf → lim g Hg < ∞) → (0 = lim g Hg → lim f Hf < ∞) →
lim (λ n, f n * g n) Hprod = lim f Hf * lim g Hg.

Axiom lim_of_inv :
∀ (f : nat → R⁺) (H : has_lim f),
lim (λ n, / f n) (inv_has_lim f H) = / lim f H.

Axiom lim_of_inv' :
∀ (f : nat → R⁺) (H : has_lim f) (Hinv : has_lim (λ n, / f n)),
lim (λ n, / f n) Hinv = / lim f H.

Axiom lim_extensionality :
∀ (f g : nat → R⁺) (Hf : has_lim f) (Hg : has_lim g), (∀ n, f n = g n) →
lim f Hf = lim g Hg.

Axiom lim_extensionality_le :
∀ (f g : nat → R⁺) (Hf : has_lim f) (Hg : has_lim g), (∀ n, f n ≤ g n) →
lim f Hf ≤ lim g Hg.

Lemma sup_le_inf :
∀ (f g : nat → R⁺), monotone f → antitone g →
(∀ n, f n ≤ g n) → sup f ≤ inf g.
Proof.
intros f g Hf Hg Hfg.
specialize (sup_is_lub f) as P.
destruct P as [_ P]. apply P.
unfold is_upper_bound. intros p [m Hp]. subst p.
specialize (inf_is_glb g) as Q.
destruct Q as [_ Q]. apply Q.
unfold is_lower_bound. intros q [n Hq]. subst q.
destruct (le_dec m n).
+ apply ennr_le_trans with (r2 := f n). 1:{ apply Hf. omega. } apply Hfg.
+ apply ennr_le_trans with (r2 := g m). 2:{ apply Hg. omega. } apply Hfg.
Qed.