Require Import Lang.Syntax Lang.Bindings.

Set Implicit Arguments.
Implicit Types V : Set.

Hint Extern 1 => match goal with
| [ |- ∀ x : ∅, _ ] => let x := fresh "x" in (intro x ; destruct x)
| [ x : ∅ |- _ ] => destruct x
| [ x : inc ?V |- _ ] => destruct x ; simpl ; crush
| [ |- context[ _ ∘ _ ] ] => unfold compose ; crush
end : core.

Fixpoint
V_map_val_id V (f : V → V) (Hf : ∀ x, f x = x)
(v : val V) {struct v} :
V_map_val f v = v
with
V_map_exp_id V (f : V → V) (Hf : ∀ x, f x = x)
(e : exp V) {struct e} :
V_map_exp f e = e
.
Proof.
+ destruct v ; crush.
+ destruct e ; crush.
Qed.

Fixpoint
V_map_map_val V1 V2 V3
(f₁ : V1 → V2) (f₂ : V2 → V3) (g : V1 → V3)
(Hf : ∀ x, f₂ (f₁ x) = g x)
(v : val V1) {struct v} :
V_map_val f₂ (V_map_val f₁ v) = V_map_val g v
with
V_map_map_exp V1 V2 V3
(f₁ : V1 → V2) (f₂ : V2 → V3) (g : V1 → V3)
(Hf : ∀ x, f₂ (f₁ x) = g x)
(e : exp V1) {struct e} :
V_map_exp f₂ (V_map_exp f₁ e) = V_map_exp g e.
Proof.
+ destruct v ; simpl ;
  repeat erewrite V_map_map_exp ;
  repeat erewrite V_map_map_val ;
  crush.
+ destruct e ; simpl ;
  repeat erewrite V_map_map_exp ;
  repeat erewrite V_map_map_val ;
  crush.
Qed.


Fixpoint
V_bind_val_id
V (f : V → val V) (Hf : ∀ x, f x = val_var x)
(v : val V) {struct v} :
V_bind_val f v = v
with
V_bind_exp_id
V (f : V → val V) (Hf : ∀ x, f x = val_var x)
(e : exp V) {struct e} :
V_bind_exp f e = e.
Proof.
+ destruct v ; crush.
+ destruct e ; crush. 
Qed.

Section section_V_bind_map.

Hint Extern 1 => match goal with
| [ |- context[ V_map_val _ (V_map_val _ _) ] ] => erewrite V_map_map_val ; crush
end : core.

Fixpoint
V_bind_map_val
(V₁ V₂₁ V₂₂ V₃ : Set)
(f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val V₃)
(g₁ : V₁ → val V₂₂) (g₂ : V₂₂ → V₃)
(Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
(v : val V₁) {struct v} :
V_bind_val f₂ (V_map_val f₁ v) = V_map_val g₂ (V_bind_val g₁ v)
with
V_bind_map_exp
(V₁ V₂₁ V₂₂ V₃ : Set)
(f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val V₃)
(g₁ : V₁ → val V₂₂) (g₂ : V₂₂ → V₃)
(Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
(e : exp V₁) {struct e} :
V_bind_exp f₂ (V_map_exp f₁ e) = V_map_exp g₂ (V_bind_exp g₁ e).
Proof.
+ destruct v ; simpl ;
  repeat erewrite V_bind_map_val ;
  repeat erewrite V_bind_map_exp ;
  crush.
+ destruct e ; simpl ;
  repeat erewrite V_bind_map_val ;
  repeat erewrite V_bind_map_exp ;
  crush.
Qed.

End section_V_bind_map.

Section section_V_bind_bind.

Hint Extern 1 => match goal with
| [ |- context[ V_bind_val _ (V_map_val _ _) ] ] => erewrite V_bind_map_val ; crush
end : core.

Fixpoint
V_bind_bind_val (V₁ V₂ V₃ : Set)
(f₁ : V₁ → val V₂) (f₂ : V₂ → val V₃)
(g : V₁ → val V₃)
(Hf : ∀ x, g x = V_bind_val f₂ (f₁ x))
(v : val V₁) {struct v} :
V_bind_val f₂ (V_bind_val f₁ v) = V_bind_val g v
with
V_bind_bind_exp (V₁ V₂ V₃ : Set)
(f₁ : V₁ → val V₂) (f₂ : V₂ → val V₃)
(g : V₁ → val V₃)
(Hf : ∀ x, g x = V_bind_val f₂ (f₁ x))
(e : exp V₁) {struct e} :
V_bind_exp f₂ (V_bind_exp f₁ e) = V_bind_exp g e
.
Proof.
+ destruct v ; simpl ;
  repeat erewrite V_bind_bind_val ;
  repeat erewrite V_bind_bind_exp ;
  crush.
+ destruct e ; simpl ;
  repeat erewrite V_bind_bind_val ;
  repeat erewrite V_bind_bind_exp ;
  crush.
Qed.

End section_V_bind_bind.
