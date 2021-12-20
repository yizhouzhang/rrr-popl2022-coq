(** This file axiomatizes the needed definitions and properties of the Lebesgue
integral. It ignores all issues of measurability, but otherwise attempts to
only axiomatize well-known results in analysis and measure theory. *)

Require Import Utf8.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.

Require Import RRR.Util.Option.
Require Import RRR.Util.Misc.
Require Import RRR.Lebesgue.Ennr.

Local Open Scope program_scope.
Local Open Scope ennr_scope.

(** * Definitions *)

(** Using [bool] instead of [Prop] for the definition of an event is a little
unusual, but allows us to define an indicator function that produces real
numbers (which are in the [Set] universe). It's very possible there are other
solutions to this problem, such as using [excluded_middle_informative]. *)
Definition Event X := X → bool.
Definition Meas A := (Event A → R⁺).

(** [ifte] is a function version of "if then else" which allows tactics like
f_equal can deal with it more easily. *)
Definition ifte {X} (a : bool) (b c : X) := if a then b else c.
Definition indicator {X} (b : Event X) : X → R⁺ := fun x => ifte (b x) 1 0.

Definition full_event {X} : Event X := const true.

Definition bool_of_dec {X Y} : sumbool X Y → bool :=
  fun xy => if xy then true else false.

(** * Axioms of integration *)

(** Assume that integration exists for all (non-negative) functions. *)
Parameter integrate : ∀ {A}, (A → R⁺) → Meas A → R⁺.
Notation "∫" := (integrate).

(** Assume the general form of linearity for integration. *)
Axiom integration_linear :
∀ {A} (μ : Meas A) (s0 s1 : R⁺) (f0 f1 : A → R⁺),
s0 * ∫ f0 μ + s1 * ∫ f1 μ = ∫ (fun x => s0 * f0 x + s1 * f1 x) μ.

(** Axiomatize the Lebesgue measure restricted to non-negative reals.
 Throw in ∞ too -- but it's just one point so it has no mass. *)
Parameter lebesgue_pos_measure : Meas R⁺.
Parameter lebesgue_measure : Meas R.
Axiom lebesgue_measure_full_event : ∞ = lebesgue_measure full_event.

(** Assume lebesgue([0, r]) = r *)
Axiom lebesgue_pos_measure_interval :
∀ (r : R⁺),
lebesgue_pos_measure (fun x => bool_of_dec (ennr_gt_dec r x)) = r.

(** Assume that Lebesgue integration can be expressed as a Riemann integral
of the "layer cake" function. (Leib and Loss, 1997).

Despite the promise in the name to relate Lebesgue and Riemann integrals, it
is phrased here as a relation just between Lebesgue and Lebesgue. Since the
Lebesuge integral is defined strictly more often than and always agrees with
the Riemann integral, this is still a valid assumption.

This assumption turns out to be very useful for proving equalities of
integrals between measure-isomorphic domains. It also can provide a way to
deal with integration by non-axiomatized measures, e.g., pushfowards.
*)
Axiom riemann_def_of_lebesgue_integration :
∀ {X} μ (f : X → R⁺),
∫ f μ =
∫ (fun r => μ (fun x => bool_of_dec (ennr_gt_dec (f x) r)))
  lebesgue_pos_measure.

(** This assumption is usually presented as the first step in the definition
of the Lebesgue integral. *)
Axiom integration_of_indicator :
∀ {A} (μ : Meas A) (ev : Event A), ∫ (indicator ev) μ = μ ev.

(** Define convenient, Haskelly syntax for working with Markov kernels as a
monad in the spirit of Giry (1980) and Panangaden (1999). For lack of a
better name, let's call the SRel+ because we're removing the subprobability
restriction from SRel. *)
Definition meas_bind {A B} (μ : Meas A) (f : A → Meas B) : Meas B :=
fun eB => ∫ (fun a => f a eB) μ.
Infix ">>=" := meas_bind (at level 20).

(** This is the associativity law for SRel+. Panangaden proved this for
subprobabilities, but his proof makes no use of that restriction, and is
therefore just as good of a proof in this instance. *)
Axiom meas_bind_assoc :
∀ {A B C} (μ : Meas A) (f : A → Meas B) (g : B → Meas C),
(μ >>= f) >>= g = μ >>= (fun a => f a >>= g).

(** Axiomatize σ-finiteness. *)
Parameter σ_finite : ∀ {A}, Meas A → Prop.

(** An actual definition of σ-finiteness here would be more challenging than
rewarding, so we instead simply state the σ-finiteness results that we will be using.
*)
Axiom leb_pos_is_σ_finite : σ_finite lebesgue_pos_measure.
Axiom leb_is_σ_finite : σ_finite lebesgue_measure.

(* Hint Resolve leb_pos_is_σ_finite leb_is_σ_finite. *)

(** We axiomitize Tonelli's theorem for all combinations of the two measures
listed above. *)
Axiom tonelli :
∀ {X Y} (f : X → Y → R⁺) (μx : Meas X) (μy : Meas Y),
σ_finite μx →
σ_finite μy →
∫ (fun x => ∫ (fun y => f x y) μy) μx =
∫ (fun y => ∫ (fun x => f x y) μx) μy.

(** * Consequences of the axioms *)

(** ** Measure combinators *)

Definition empty_meas X : Meas X := fun x => 0.
Arguments empty_meas {X} _ /.

Definition dirac {A} (a : A) : Meas A := fun ev => indicator ev a.
Arguments dirac {_} _ _ /.

Definition preimage {A B} (f : A → B) : (B → bool) → (A → bool) :=
fun eB a => eB (f a).
Arguments preimage {_ _} _ _ _ /.

Definition pushforward {A B} (μ : Meas A) (f : A → B) : Meas B :=
  μ ∘ preimage f.

(** Convert emptiness in an option to emptiness in a measure. *)
Definition option_meas {A} (oμ : option (Meas A)) : Meas A :=
fromOption empty_meas oμ.

Definition meas_option {A} (μo : Meas (option A)) : Meas A :=
fun ev => μo (
  fun oa =>
    match oa with
    | Some x => ev x
    | _ => false
    end
).

(** Two ways to reweight a [Meas A].
[unif_score_meas] reweights the entire measure by a constant.
[score_meas] reweights dependent on each element in [A].
*)
Definition unif_score_meas {X} (s : R⁺) (μ : Meas X) : Meas X :=
fun A => μ A * s.
Arguments unif_score_meas {_} _ _ _ /.

Definition score_meas {X} (w : X → R⁺) (μ : Meas X) : Meas X :=
  μ >>= (fun x A => w x * indicator A x).


(** ** Lemmas about integration *)

(** Tactic for showing [∫ f dμ = ∫ g dμ] by pointwise equality of [f] and [g]. *)
Ltac integrand_extensionality x :=
match goal with
| [ |- _ = _ :> R⁺ ] => idtac
| [ |- _ = _ :> Meas _ ] => let A := fresh "A" in extensionality A
| [ |- _ = _ :> _ → R⁺ ] => let A := fresh "A" in extensionality A
end;
refine (f_equal2 ∫ _ eq_refl);
extensionality x.

(** Derive some more immediately useful forms of linearity. *)

Lemma integration_linear_plus:
  ∀ {A} (μ : Meas A) (f0 f1 : A → R⁺),
    ∫ f0 μ + ∫ f1 μ = ∫ (fun x => f0 x + f1 x) μ.
Proof.
  intros.
  replace (∫ f0 μ + ∫ f1 μ) with (1 * ∫ f0 μ + 1 * ∫ f1 μ) by ring.
  rewrite integration_linear.
  integrand_extensionality x.
  ring.
Qed.

Axiom integration_linear_minus:
∀ {A} (μ : Meas A) (f0 f1 : A → R⁺),
(∀ a, f1 a ≤ f0 a) →
∫ f0 μ - ∫ f1 μ = ∫ (fun x => f0 x - f1 x) μ.

Lemma integration_linear_mult_r
{A} (μ : Meas A) (r : R⁺) (f : A → R⁺) :
∫ (fun x => f x * r) μ =
∫ f μ * r.
Proof.
replace (∫ f μ * r) with (r * ∫ f μ + 0 * ∫ f μ) by ring.
rewrite integration_linear.
integrand_extensionality x.
ring.
Qed.

Lemma integration_linear_mult_l
{A} (μ : Meas A) (r : R⁺) (f : A → R⁺) :
∫ (fun x => r * f x) μ =
r * ∫ f μ.
Proof.
setoid_rewrite ennr_mul_comm.
apply integration_linear_mult_r.
Qed.

Lemma integration_linear_in_meas_l
{A} (r : R⁺) (μ : Meas A) (f : A → R⁺) :
∫ f (fun ev => r * μ ev) =
r * ∫ f μ.
Proof.
setoid_rewrite riemann_def_of_lebesgue_integration.
rewrite <- integration_linear_mult_l.
reflexivity.
Qed.

Lemma integration_linear_in_meas_r
{A} (r : R⁺) (μ : Meas A) (f : A → R⁺) :
∫ f (fun ev => μ ev * r) =
∫ f μ * r.
Proof.
setoid_rewrite riemann_def_of_lebesgue_integration.
rewrite <- integration_linear_mult_r.
reflexivity.
Qed.

Lemma integration_of_const
{X} (r : R⁺) (f : X → R⁺) (μ : Meas X) :
(∀ x, f x = r) → ∫ f μ = r * μ full_event.
Proof.
intros.
replace f with (fun x => f x * 1) by (extensionality t; ring).
setoid_rewrite H.
rewrite integration_linear_mult_l.
replace (fun _ => 1) with (@indicator X full_event) by reflexivity.
rewrite integration_of_indicator.
ring.
Qed.

Lemma integration_of_0
{A} (μ : Meas A) : ∫ (fun _ => 0) μ = 0.
Proof.
replace 0 with (0 * 0) by ring.
rewrite integration_linear_mult_r.
ring.
Qed.

(** Lemmas about inequality *)
Axiom integrand_extensionality_lt :
∀ {A} (μ : Meas A) (f1 f2 : A → R⁺),
(∀ a, f1 a < f2 a) →
∫ f1 μ < ∫ f2 μ.

Axiom integrand_extensionality_le :
∀ {A} (μ : Meas A) (f1 f2 : A → R⁺),
(∀ a, f1 a ≤ f2 a) →
∫ f1 μ ≤ ∫ f2 μ.

Axiom integrand_extensionality_le_meas :
∀ {A} (μ1 μ2 : Meas A) (f1 f2 : A → R⁺),
(∀ a, f1 a ≤ f2 a) →
(∀ A, μ1 A ≤ μ2 A) →
∫ f1 μ1 ≤ ∫ f2 μ2.

(** Some lemmas about integrating by the new measures *)
Lemma integration_of_pushforward
{A B} (f : A → B) (g : B → R⁺) (μ : Meas A) :
∫ (g ∘ f) μ = ∫ g (pushforward μ f).
Proof.
setoid_rewrite riemann_def_of_lebesgue_integration.
unfold pushforward, preimage, compose.
trivial.
Qed.

Lemma integration_wrt_dirac
{A} (a : A) (f : A → R⁺) :
∫ f (dirac a) = f a.
Proof.
setoid_rewrite riemann_def_of_lebesgue_integration.
unfold dirac.
setoid_rewrite integration_of_indicator.
rewrite lebesgue_pos_measure_interval.
reflexivity.
Qed.

Lemma integration_wrt_empty
{A} (f : A → R⁺) :
∫ f empty_meas = 0.
Proof.
setoid_rewrite riemann_def_of_lebesgue_integration.
unfold empty_meas.
rewrite integration_of_0.
reflexivity.
Qed.

Axiom integration_wrt_score_meas : ∀ X (f w : X → R⁺) (μ : Meas X),
∫ f (score_meas w μ) = ∫ (λ x, f x * w x) μ.
(* Requires Radon–Nikodym to find the pushforward *)

Lemma bind_meas_option {A B} μ (f : A → Meas B) :
meas_option μ >>= f =
μ >>= (fun x ev => option0 (flip f ev <$> x)).
Proof.
intros.
extensionality ev.
setoid_rewrite riemann_def_of_lebesgue_integration.
integrand_extensionality t.
unfold meas_option.
f_equal.
extensionality x.
destruct x; cbn; auto.
destruct ennr_gt_dec; auto.
contradict e.
destruct t; cbn; auto.
apply RIneq.Rle_not_lt.
auto.
Qed.

(** The remaining two monad laws for SRel+ *)

Lemma meas_id_left {A B} a (f : A → Meas B) :
(dirac a >>= f) = f a.
Proof.
extensionality ev.
unfold ">>=".
rewrite integration_wrt_dirac.
reflexivity.
Qed.

Lemma meas_id_right {A} (μ : Meas A) :
(μ >>= dirac) = μ.
Proof.
extensionality ev.
unfold ">>=", dirac.
apply integration_of_indicator.
Qed.

Definition meas_join {A} (μ : Meas (Meas A)) : Meas A :=
μ >>= (fun x => x).

Definition kernel A B := A → Meas B.

(** * Measures that may be safely interchanged *)

(** Tonelli's theorem will be too restricted to be of immediate use in
dealing with some of our measures. We will need to prove that a wider class
of measures than just σ-finite ones can be involved in an integral
interchange. *)
Class interchangeable {A B} (μa : Meas A) (μb : Meas B) : Prop :=
  interchange :
  ∀ {C} (f : A → B → Meas C),
  μa >>= (fun a => μb >>= (fun b => f a b)) =
  μb >>= (fun b => μa >>= (fun a => f a b))
.

(** [interchangeable] is a symmetric relation. Unfortunately we can't use the
[Symmetry] typeclass because it's a relation between different types. *)
Definition interchangeable_sym {A B} (μa : Meas A) (μb : Meas B) :
interchangeable μa μb → interchangeable μb μa.
Proof.
repeat intro.
symmetry.
apply H.
Qed.

Instance σ_finite_is_interchangeable {A B} (μa : Meas A) (μb : Meas B) :
σ_finite μa →
σ_finite μb →
interchangeable μa μb.
Proof.
repeat intro.
extensionality ec.
unfold ">>=".
apply tonelli ; auto.
Qed.

Instance score_meas_interchangeable {X} (μX : Meas X) (w : X → R⁺) :
∀ {Y} (μy : Meas Y),
interchangeable μX μy →
interchangeable (score_meas w μX) μy.
Proof.
repeat intro.
unfold score_meas.
setoid_rewrite meas_bind_assoc.
rewrite <- H ; clear H.
unfold ">>=".
extensionality eC.
integrand_extensionality x.
setoid_rewrite integration_linear_in_meas_l.
setoid_rewrite integration_linear_mult_l.
f_equal.
fold (dirac x).
setoid_rewrite integration_wrt_dirac.
reflexivity.
Qed.

Instance pushforward_interchangeable
{X Y} (μ : Meas X) (f : X → Y)
{Z} (μz : Meas Z) :
interchangeable μ μz →
interchangeable (pushforward μ f) μz.
Proof.
intros H ? g.
unfold ">>=".
setoid_rewrite <- (integration_of_pushforward f).
unfold compose.
change (
  (λ ev, ∫ (λ x, ∫ (λ z : Z, (g ∘ f) x z ev) μz) μ) =
  (λ ev, ∫ (λ z, ∫ (λ x : X, (g ∘ f) x z ev) μ) μz)
).
apply H.
Qed.

Instance meas_option_interchangeable
{X} (μ : Meas (option X))
{Y} (μy : Meas Y) :
interchangeable μ μy →
interchangeable (meas_option μ) μy.
Proof.
intros H ? f.
setoid_rewrite bind_meas_option.
rewrite <- H.
integrand_extensionality ox.
destruct ox; cbn; auto.
setoid_rewrite integration_of_0.
trivial.
Qed.

Lemma bind_interchangeable
{X Y} (μ : Meas X) (f : X → Meas Y)
{Z} (μz : Meas Z) :
interchangeable μ μz →
(∀ x, interchangeable (f x) μz) →
interchangeable (μ >>= f) μz.
Proof.
intros H1 H2 ? g.
repeat intro.
setoid_rewrite meas_bind_assoc.
rewrite <- H1.
setoid_rewrite H2.
reflexivity.
Qed.

(** ** Other lemmas *)

Lemma coarsening
{X} (M : Event X → Event X → Prop)
(μ₁ μ₂ : Meas X)
(f₁ f₂ : X → R⁺) :
(∀ A₁ A₂, M A₁ A₂ → μ₁ A₁ = μ₂ A₂) →
(∀ (B : Event R⁺), M (preimage f₁ B) (preimage f₂ B)) →
∫ f₁ μ₁ = ∫ f₂ μ₂.
Proof.
intros Hμ Hf.
setoid_rewrite riemann_def_of_lebesgue_integration.
integrand_extensionality t.
apply Hμ.
unfold preimage in Hf.
apply Hf with (B := λ r, bool_of_dec (ennr_gt_dec r t)).
Qed.

Axiom integration_wrt_redundant_var : ∀ X
(f : option (nat * X) → R⁺) (g : option X → R⁺)
(μ : Meas (option (nat * X))) (ν : Meas (option X)),
f None = g None →
(∀ n x, f (Some (n, x)) = g (Some x)) →
(∀ X, μ (λ y, match y with
  | Some (_, x) => X (Some x)
  | None => X None
  end) = ν X) →
∫ f μ = ∫ g ν.

(** Monotone Convergence Theorem *)

Axiom interchange_sup_integration :
∀ X (f : X → nat → R⁺) (μ : Meas X),
(∀ x, monotone (f x)) →
sup (λ n, ∫ (λ x, f x n) μ) = ∫ (λ x, sup (f x)) μ.

Axiom interchange_sup_integration_meas :
∀ X (f : X → nat → R⁺) (μ : nat → Meas X),
(∀ x, monotone (f x)) →
(∀ X, monotone (λ n, μ n X)) →
sup (λ n, ∫ (λ x, f x n) (μ n)) = ∫ (λ x, sup (f x)) (λ X, sup (λ n, μ n X)).

Axiom interchange_inf_integration :
∀ X (f : X → nat → R⁺) (μ : Meas X),
(∀ x, antitone (f x)) →
inf (λ n, ∫ (λ x, f x n) μ) = ∫ (λ x, inf (f x)) μ.

Axiom interchange_inf_integration_meas :
∀ X (f : X → nat → R⁺) (μ : nat → Meas X),
(∀ x, antitone (f x)) →
(∀ X, antitone (λ n, μ n X)) →
inf (λ n, ∫ (λ x, f x n) (μ n)) = ∫ (λ x, inf (f x)) (λ X, inf (λ n, μ n X)).

(* left open, right closed interval *)
Axiom Rinterval_dec' : ∀ (a b r : R), {(a < r ∧ r ≤ b)%R} + {¬ (a < r ∧ r ≤ b)%R}.
  
Axiom integral_over_intervals : ∀ (a b c : R) (e : R → R⁺) (H : (a ≤ b ≤ c)%R),
    ∫ (λ r : R, e r * (if Rinterval_dec a c r then 1 else 0)) lebesgue_measure
    = ∫ (λ r : R, e r * (if Rinterval_dec a b r then 1 else 0)) lebesgue_measure
      + ∫ (λ r : R, e r * (if Rinterval_dec' b c r then 1 else 0)) lebesgue_measure.

Axiom lebesgue_measure_of_inverval : ∀ (a b : R) (H : (0 <= b - a)%R),
    ∫ (λ x : R, if Rinterval_dec a b x then 1 else 0) lebesgue_measure
    = finite (b - a) H.

Axiom lebesgue_measure_of_inverval' : ∀ (a b : R) (H : (0 <= b - a)%R),
    ∫ (λ x : R, if Rinterval_dec' a b x then 1 else 0) lebesgue_measure
    = finite (b - a) H.
