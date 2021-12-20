Require Import Lang.Syntax.
Require Import Lang.Bindings.
Require Import Lang.BindingsFacts.
Require Import Lang.Static.

Set Implicit Arguments.
Implicit Types V : Set.

Fixpoint V_map_wf_exp V V'
(Γ : V → ty) (e : exp V) T (Wf_e : wf_exp Γ e T)
(f : V → V')
(Γ' : V' → ty) (HΓ : ∀ x, Γ x = Γ' (f x))
{struct Wf_e} :
wf_exp Γ' (V_map_exp f e) T
with V_map_wf_val V V'
(Γ : V → ty) (v : val V) T (Wf_v : wf_val Γ v T)
(f : V → V')
(Γ' : V' → ty) (HΓ : ∀ x, Γ x = Γ' (f x))
{struct Wf_v} :
wf_val Γ' (V_map_val f v) T.
Proof.
{
destruct Wf_e; simpl.
+ constructor. eapply V_map_wf_val; eassumption.
+ econstructor.
  - eapply V_map_wf_exp; eassumption.
  - eapply V_map_wf_exp; eassumption.
+ econstructor.
  - eapply V_map_wf_exp; eassumption.
  - eapply V_map_wf_exp. 1:{ eassumption. }
    destruct x as [|x]; simpl; auto.
+ econstructor.
  - eapply V_map_wf_exp; eassumption.
  - eapply V_map_wf_exp; eassumption.
+ constructor. eapply V_map_wf_exp; eassumption.
+ constructor; eapply V_map_wf_exp; eassumption.
+ constructor. eapply V_map_wf_exp; eassumption.
+ constructor. eapply V_map_wf_exp; eassumption.
+ constructor.
}
{
destruct Wf_v; simpl.
+ rewrite HΓ. constructor.
+ constructor.
+ constructor.
+ constructor.
+ econstructor. eapply V_map_wf_exp. 1:{ eassumption. }
  destruct x as [|x]; simpl; auto.
+ constructor. eapply V_map_wf_exp. 1:{ eassumption. }
  destruct x as [|x]; simpl; auto.
+ constructor.
  - eapply V_map_wf_val; eassumption.
  - eapply V_map_wf_val; eassumption.
+ constructor.
+ constructor. 2:{ assumption. } eapply V_map_wf_exp; eassumption.
}
Qed.

Fixpoint V_bind_wf_exp V V'
(Γ : V → ty) (e : exp V) T (Wf_e : wf_exp Γ e T)
(f : V → val V')
(Γ' : V' → ty) (HΓ : ∀ x, wf_val Γ' (f x) (Γ x))
{struct Wf_e} :
wf_exp Γ' (V_bind_exp f e) T
with V_bind_wf_val V V'
(Γ : V → ty) (v : val V) T (Wf_v : wf_val Γ v T)
(f : V → val V')
(Γ' : V' → ty) (HΓ : ∀ x, wf_val Γ' (f x) (Γ x))
{struct Wf_v} :
wf_val Γ' (V_bind_val f v) T.
{
destruct Wf_e; simpl.
+ constructor. eapply V_bind_wf_val; eassumption.
+ econstructor.
  - eapply V_bind_wf_exp; eassumption.
  - eapply V_bind_wf_exp; eassumption.
+ econstructor.
  - eapply V_bind_wf_exp; eassumption.
  - eapply V_bind_wf_exp. 1:{ eassumption. }
    destruct x as [|x]; simpl. 1:{ constructor. }
    eapply V_map_wf_val. 1:{ apply HΓ. } 1:{ reflexivity. }
+ econstructor.
  - eapply V_bind_wf_exp; eassumption.
  - eapply V_bind_wf_exp; eassumption.
+ constructor. eapply V_bind_wf_exp; eassumption.
+ constructor; eapply V_bind_wf_exp; eassumption.
+ constructor. eapply V_bind_wf_exp; eassumption.
+ constructor. eapply V_bind_wf_exp; eassumption.
+ constructor.
}
{
destruct Wf_v; simpl.
+ apply HΓ.
+ constructor.
+ constructor.
+ constructor.
+ econstructor. eapply V_bind_wf_exp. 1:{ eassumption. }
  destruct x as [|x]; simpl. 1:{ constructor. }
  eapply V_map_wf_val. 1:{ apply HΓ. } 1:{ reflexivity. }
+ constructor. eapply V_bind_wf_exp. 1:{ eassumption. }
  destruct x as [|x]; simpl. 1:{ constructor. }
  eapply V_map_wf_val. 1:{ apply HΓ. } 1:{ reflexivity. }
+ constructor.
  - eapply V_bind_wf_val; eassumption.
  - eapply V_bind_wf_val; eassumption.
+ constructor.
+ constructor. 2:{ assumption. } eapply V_bind_wf_exp; eassumption.
}
Qed.
