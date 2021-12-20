Require Import Utf8 Lia.
Require Import Coq.Relations.Relations.
Require Import FunctionalExtensionality.
Require Import CpdtTactics.
Set Implicit Arguments.

Declare Scope lt2_scope.
Delimit Scope lt2_scope with lt2.

Lemma Acc_trans (A : Type) (R : relation A) :
∀ x, Acc R x → Acc (clos_trans A R) x.
Proof.
intros x H.
induction H as [ x Hx IHx ] ; constructor ; intros y Ryx.
induction Ryx.
+ auto.
+ eapply Acc_inv ; eauto.
Qed.

Inductive lt2_base : nat * nat → nat * nat → Prop :=
| lt2_base_1 : ∀ m' m n, m' < m → lt2_base (m', n) (m, n)
| lt2_base_2 : ∀ m n' n, n' < n → lt2_base (m, n') (m, n)
.

Lemma lt2_base_wf_aux :
well_founded lt → forall m, Acc lt m → forall n, Acc lt n → Acc lt2_base (m, n).
Proof.
intros Hlt x Hx.
induction Hx as [x _ IHaccx].
intros y Hy.
induction Hy as [y _ IHaccy].
constructor.
intros (x', y').
inversion 1 ; subst ; auto.
Qed.

Lemma lt2_base_wf : well_founded lt2_base.
Proof.
intros (x, y).
apply lt2_base_wf_aux ; apply Wf_nat.lt_wf.
Qed.

Definition lt2 := clos_trans _ lt2_base.

Lemma lt2_wf : well_founded lt2.
Proof.
intros (x, y).
unfold well_founded.
apply Acc_trans.
apply lt2_base_wf.
Qed.

Lemma lt2_wf_ind (P : nat * nat → Prop) :
(∀ y, (∀ x, lt2 x y → P x) → P y) →
∀ z, P z.
Proof.
intros.
elim (lt2_wf z).
auto.
Qed.

Inductive lt2_alt : nat * nat → nat * nat → Prop :=
| lt2_alt_1 : ∀ m' n' m n, m' < m → n' ≤ n → lt2_alt (m', n') (m, n)
| lt2_alt_2 : ∀ m' n' m n, m' ≤ m → n' < n → lt2_alt (m', n') (m, n)
.

Infix "<" := lt2_alt : lt2_scope.

Section section_lt2_alt.
Hint Constructors lt2_alt:core.

Lemma lt2_is_lt2_alt m' n' m n :
lt2 (m', n') (m, n) ↔ lt2_alt (m', n') (m, n).
Proof.
split.
{
induction 1 as [ [x' y'] [x y] H | [x'' y''] [x' y'] [x y] H'' IH'' H' IH' ].
+ inversion H ; subst ; auto.
+ inversion IH'' ; inversion IH' ; subst.
  - apply lt2_alt_1 ; lia.
  - apply lt2_alt_1 ; lia.
  - apply lt2_alt_1 ; lia.
  - apply lt2_alt_2 ; lia.
}
{
intro H ; inversion H ; subst ; clear H.
+ match goal with [ H : _ ≤ _ |- _ ] => induction H as [ | ? ? IH ] end.
  - repeat constructor ; auto.
  - eapply t_trans ; [ apply IH | ].
    apply t_step.
    constructor ; lia.
+ match goal with [ H : _ ≤ _ |- _ ] => induction H as [ | ? ? IH ] end.
  - repeat constructor ; auto.
  - eapply t_trans ; [ apply IH | ].
    apply t_step.
    constructor ; lia.
}
Qed.

End section_lt2_alt.

Ltac lt2_solve :=
repeat match goal with
| [ W : Acc lt2 (?n2, ?m2) |- Acc lt2 (?n1, ?m1) ] =>
  apply (Acc_inv W) ; simpl
| [ |- lt2 (?n2, ?m2) (?n1, ?m1) ] =>
  rewrite lt2_is_lt2_alt
| [ |- lt2_alt (?n2, ?m2) (S ?n1, ?m1) ] =>
  apply lt2_alt_1 ; lia
| [ |- lt2_alt (?n2, ?m2) (?n1, S ?m1) ] =>
  apply lt2_alt_2 ; lia
end.