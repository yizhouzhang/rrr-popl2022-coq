Require Import Omega.
Require Import RRR.Lang.Lang.
Require Import RRR.Lebesgue.Lebesgue.
Require Import RRR.Rel.Relations.
Require Import Lra.

Lemma adequacy e₁ e₂ :
ERel_open ∅→ ℝ e₁ e₂ →
∀ N₁, ORel N₁ e₁ e₂.
Proof.
intros [[_ _] He].
intros N₁.
assert (N₁ <= N₁) as le_N₁_refl ; [ omega | ].
assert (EnvRel ∅→ N₁ ∅→ ∅→) as Hempty.
1:{ intro x ; destruct x. }
specialize (He N₁ ∅→ ∅→ Hempty).
repeat (erewrite V_bind_exp_id in He ; [ | intro x; destruct x ]).
specialize (He N₁ le_N₁_refl ktx_hole ktx_hole).
assert (KRel ℝ N₁ ktx_hole ktx_hole) as Hhole.
1:{
  clear.
  intros N₁' HN₁' v₁ v₂ Hv. destruct Hv as [r [? ?]].
  subst. simpl. split.
  - rewrite μNS_val. apply μNS_inf_le_1.
  - intro. rewrite μTV_val.
    unfold μTV_sup. erewrite sup_of_constant.
    2:{ intro. rewrite μTV_val. reflexivity. }
    apply ennr_le_refl.
}
apply He. apply Hhole.
Qed.