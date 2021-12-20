Require Import Utf8.
Require Import Reals.
Require Import Lebesgue.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

(** Entropy is the source of all randomness in an evaluation. The particular
representation we choose is the Hilbert cube #(ℕ → [0, 1])#. In particular,
the properties we use on it are that an entropy source can be split into two
entropy sources through the operations [πL] and [πR], which are defined here
and axiomatized to be IID in [integration_πL_πR]. When it actually comes to
using an entropy [t], it is also convenient to split it into arbitrarily many
indepent parts, as (π 0 t), (π 1 t), ... *)

Definition entropy := nat → { r : R | (0 ≤ r ≤ 1)%R }.

(** The projection functions don't muck with any real numbers, just shuffle
indices around. [πL_n] and the like are the exact index shuffling needed for
[πL] and the like. *)
Definition πL (t : entropy) : entropy := λ n, t (n + n)%nat.
Definition πR (t : entropy) : entropy := λ n, t (S (n + n))%nat.
Notation πU t := (proj1_sig (πL t 0%nat)).

(** [join] is the inverse of projections, that is [t = join (πL t) (πR t)].
This is later proved as [join_πL_πR]. This is finally automated in the tactic
[π_join]. *)
Definition join (tL tR : entropy) : entropy :=
fun n =>
  if Nat.even n
  then tL (Nat.div2 n)
  else tR (Nat.div2 n).

Lemma πL_join tL tR : πL (join tL tR) = tL.
Proof.
extensionality n.
unfold πL, join.
assert (Nat.even (n + n) = true). {
  induction n; simpl; auto.
  replace (n + S n)%nat with (S (n + n)); auto.
}
rewrite H.
f_equal.
fold (Nat.double n).
rewrite Nat.double_twice.
apply Nat.div2_double.
Qed.

Lemma πR_join tL tR : πR (join tL tR) = tR.
Proof.
extensionality n.
unfold πR, join.
assert (Nat.even (S (n + n)) = false). {
  induction n; simpl; auto.
  replace (n + S n)%nat with (S (n + n)); auto.
}
rewrite H.
f_equal.
fold (Nat.double n).
rewrite Nat.double_twice.
apply Nat.div2_succ_double.
Qed.

Lemma join_πL_πR t : join (πL t) (πR t) = t.
Proof.
extensionality n.
unfold join, πL, πR.
destruct (Nat.Even_or_Odd n). {
  rewrite (proj2 (Nat.even_spec n)); auto.

  f_equal.
  fold (Nat.double (Nat.div2 n)).
  rewrite <- Div2.even_double; auto.
  apply Even.even_equiv; auto.
} {
  pose proof (proj2 (Nat.odd_spec n) H).
  rewrite <- Nat.negb_even in H0.
  apply Bool.negb_true_iff in H0.
  rewrite H0.

  f_equal.
  change (S (Nat.double (Nat.div2 n)) = n).
  rewrite <- Div2.odd_double; auto.
  apply Even.odd_equiv; auto.
}
Qed.

Fixpoint π (n : nat) (t : entropy) : entropy :=
match n with
| O => πL t
| S n' => π n' (πR t)
end.
Arguments π _ _ _ : simpl never.

Fixpoint π_leftover (n : nat) (t : entropy) : entropy :=
match n with
| O => t
| S n' => π_leftover n' (πR t)
end.
Arguments π_leftover _ _ _ : simpl never.

Lemma π_O_join (tl tr : entropy) : π 0 (join tl tr) = tl.
Proof.
apply πL_join.
Qed.

Lemma π_S_join (n : nat) (tl tr : entropy) : π (S n) (join tl tr) = π n tr.
Proof.
unfold π.
fold π.
rewrite πR_join.
auto.
Qed.

Ltac π_join := repeat rewrite ?π_O_join, ?π_S_join in *.

(** Axiomatize the stock measure on traces. *)

(** Assume that [entropy] has a probability measure on it *)
Axiom μentropy : Meas entropy.
Axiom μentropy_is_a_probability_measure : μentropy full_event = 1.
Axiom μentropy_is_σ_finite : σ_finite μentropy.

(** This axiom states that entropy can be split into 2 IID entropies. *)
Axiom integration_πL_πR : ∀ (g : entropy → entropy → R⁺),
∫ (fun t => g (πL t) (πR t)) μentropy =
∫ (fun tL => ∫ (fun tR => g tL tR) μentropy) μentropy.

Axiom integration_πU_lebesgue : ∀ (f : R → R⁺),
∫ (λ (t : entropy), f (proj1_sig (t 0%nat))) μentropy =
∫ (λ r, f r * (if Rinterval_dec 0 1 r then 1 else 0)) lebesgue_measure.

(** Use the fact that [μentropy] is a probability measure to lift constant
functions out of integrals. *)
Lemma integration_const_entropy :
∀ (v : R⁺) (f : entropy → R⁺),
(∀ x, f x = v) → ∫ f μentropy = v.
Proof.
intros.
replace f with (fun x => f x * 1) by (extensionality x; ring).
setoid_rewrite H.
rewrite integration_of_const with (r := v).
1: {
  rewrite μentropy_is_a_probability_measure.
  ring.
}
intro; ring.
Qed.

(** A particular entropy value that is an infinite sequence of 0's. *)
Definition entropy0 : entropy.
Proof.
intro n.
refine (exist _ 0%R _).
split.
+ right; ring. 
+ left; prove_sup.
Defined.