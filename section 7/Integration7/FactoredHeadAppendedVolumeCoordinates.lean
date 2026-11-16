module

public import Integration7.FactoredHeadRetainedLabels
public import Integration7.HeadAppendVolumeCoordinates
public import Integration7.UnarySpecialHeadPreparations
public import Integration7.NativeVolumeDomains

@[expose] public section

/-! A factored unary head has the literal coefficient, old fibre, new
head coordinate order, including any appended functional RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.realSpace
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {a b l d k p : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {Q : DefSet (M := M) S 0 l}
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (θ : Fin (a+d) → Fin l)
variable (L : RVLabelConstraintSpecialPreparation T H Q (θ ∘ Fin.castAdd d) P)

private theorem compose_append {α β : Type} {r s : ℕ} (f : α → β) (u : Fin r → α) (v : Fin s → α) :
    f ∘ Fin.append u v=Fin.append (f ∘ u) (f ∘ v) := by
  funext i
  exact Fin.addCases (fun j => by simp only [Function.comp_apply,Fin.append_left])
    (fun j => by simp only [Function.comp_apply,Fin.append_right]) i

private theorem append_assoc_one {α : Type} {r s : ℕ} (u : Fin r → α) (v : Fin s → α) (w : Fin 1 → α) :
    Fin.append (Fin.append u v) w=Fin.append u (Fin.append v w) := by
  rw [Fin.append_assoc]
  funext i
  exact congrArg (Fin.append u (Fin.append v w)) (Fin.ext rfl)

theorem factored_head_product_appended_coordinates (hB : IsRVPullback (carrier B))
    (σ : Fin (p+1) → Fin d) (τ : Fin (k+1) → Fin a) (u : rawVolumeContractionLabels hc (headImage L.target)) :
    u.val ∘ Fin.append (m := p+1) (n := (k+1)+1) (L.headParameters ∘ θ ∘ Fin.natAdd a ∘ σ)
      (L.headProjection ∘ headAppendVolumeIndex (unarySpecialHeadPreparation T hB) τ) =
    Fin.append (m := p+1) (n := (k+1)+1)
      (u.val ∘ fun j => Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (θ (Fin.natAdd a (σ j)))))
      (Fin.append (m := k+1) (n := 1)
        (u.val ∘ fun j => Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (θ (Fin.castAdd d (τ j)))))
        (fun _ : Fin 1 => u.val (0 : Fin (1+L.arity)))) := by
  let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
  funext j
  refine Fin.addCases (m := p+1) (n := (k+1)+1) (fun j => ?_) (fun j => ?_) j
  · simp only [Function.comp_apply,Fin.append_left]
    exact L.carried_head_suffix q (θ (Fin.natAdd a (σ j)))
  · refine Fin.addCases (m := k+1) (n := 1) (fun j => ?_) (fun j => ?_) j
    · simp only [Function.comp_apply,Fin.append_right,Fin.append_left,headAppendVolumeIndex,headSelectedLabelIndex]
      exact L.prepared_head_suffix q (τ j)
    · have hj : j=0 := Subsingleton.elim _ _
      subst j
      simp only [Function.comp_apply,Fin.append_right,headAppendVolumeIndex,
        RVLabelConstraintSpecialPreparation.headProjection,Fin.append_left]
      rfl

theorem factored_head_product_source_coordinates (hB : IsRVPullback (carrier B))
    (σ : Fin (p+1) → Fin d) (τ : Fin (k+1) → Fin a) (u : rawVolumeContractionLabels hc (headImage L.target)) :
    u.val ∘ headAppendVolumeIndex L.head
      (θ ∘ Fin.append (m := p+1) (n := k+1) (Fin.natAdd a ∘ σ) (Fin.castAdd d ∘ τ)) =
    u.val ∘ Fin.append (m := p+1) (n := (k+1)+1) (L.headParameters ∘ θ ∘ Fin.natAdd a ∘ σ)
      (L.headProjection ∘ headAppendVolumeIndex (unarySpecialHeadPreparation T hB) τ) := by
  rw [factored_head_product_appended_coordinates hc θ L hB σ τ u]
  change u.val ∘ Fin.append
    ((fun j => Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) j)) ∘ θ ∘
      Fin.append (m := p+1) (n := k+1) (Fin.natAdd a ∘ σ) (Fin.castAdd d ∘ τ))
    (fun j : Fin 1 => Fin.castAdd L.arity j) = _
  rw [compose_append]
  have hOld := compose_append
    (u.val ∘ (fun j => Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) j)) ∘ θ)
    (Fin.natAdd a ∘ σ) (Fin.castAdd d ∘ τ)
  simp only [Function.comp_assoc] at hOld ⊢
  rw [hOld,append_assoc_one]
  have hTag : (u.val ∘ fun j : Fin 1 => Fin.castAdd L.arity j) = fun _ : Fin 1 => u.val 0 := by
    funext j
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    rfl
  rw [hTag]
  rfl
end IntegrationInACVF.Section7
