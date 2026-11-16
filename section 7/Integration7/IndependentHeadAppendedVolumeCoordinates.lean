module

public import Integration7.IndependentHeadVolumeProductCharts
public import Integration7.HeadAppendVolumeCoordinates
public import Integration7.UnarySpecialHeadPreparations

@[expose] public section

/-! The independent product chart has exactly the appended order:
coefficient coordinates, old fibre coordinates, then the new head tag.
Its density is the product of the literal original retained labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {a b d p k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {A : DefSet (M := M) (C.base : Set M) 1 a} {B : DefSet (M := M) (C.base : Set M) 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) (C.base : Set M) 1 (a+d)}
variable {Q : DefSet (M := M) (C.base : Set M) 0 (a+d)}
variable (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
variable (R : DefSet (M := M) (C.base : Set M) 0 d)
variable (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R)

theorem independent_head_appended_volume_coordinates (hPullback : IsRVPullback (carrier B))
    (σ : Fin (p+1) → Fin d) (ρ : Fin (k+1) → Fin a)
    (u : rawVolumeContractionLabels hc (headImage L.target)) :
    (independentHeadProductCoordinateObject hc C L σ (headAppendVolumeIndex (unarySpecialHeadPreparation T hPullback) ρ)).value u =
      Fin.append
        (u.val ∘ (fun j => Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (Fin.natAdd a (σ j)))))
        (Fin.append
          (u.val ∘ (fun j => Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (Fin.castAdd d (ρ j)))))
          (fun _ : Fin 1 => u.val (0 : Fin (1+L.arity)))) := by
  let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
  change u.val ∘ Fin.append (L.headParameters ∘ Fin.natAdd a ∘ σ)
    (L.headProjection ∘ headAppendVolumeIndex (unarySpecialHeadPreparation T hPullback) ρ) = _
  funext j
  refine Fin.addCases (m := p+1) (n := (k+1)+1) (fun j => ?_) (fun j => ?_) j
  · simp only [Function.comp_apply,Fin.append_left]
    exact L.head_coefficient_old_labels q (σ j)
  · refine Fin.addCases (m := k+1) (n := 1) (fun j => ?_) (fun j => ?_) j
    · simp only [Function.comp_apply,Fin.append_right,Fin.append_left,headAppendVolumeIndex,headSelectedLabelIndex]
      exact L.head_prepared_old_labels q (ρ j)
    · have hj : j=0 := Subsingleton.elim _ _
      subst j
      simp only [Function.comp_apply,Fin.append_right,headAppendVolumeIndex,
        RVLabelConstraintSpecialPreparation.headProjection,Fin.append_left]
      rfl

theorem independent_head_product_original_density
    (σ : Fin (p+1) → Fin d) (τ : Fin (k+1) → Fin (1+b)) (δ : Fin d) (ε : Fin a)
    (hR : ∀ t : Fin (p+1) → RV (M := M), {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
    (hB : ∀ t : Fin (k+1) → RV (M := M), {r : Fin (1+b) → RV (M := M) | (Fin.elim0,r) ∈ carrier (headImage B) ∧ r ∘ τ=t}.Finite)
    (hδ : ∀ q : R, (q.val.2 δ).val ≠ iRVZero)
    (hε : ∀ q : headImage B, (q.val.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) ε))).val ≠ iRVZero)
    (u : (independentHeadProductVolumeObject hc C L R hQ σ τ δ
      (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) ε)) hR hB hδ hε).underlying.obj.domain) :
    (independentHeadProductVolumeObject hc C L R hQ σ τ δ
      (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) ε)) hR hB hδ hε).form.value u =
      u.val (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (Fin.natAdd a δ))) *
      u.val (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (Fin.castAdd d ε))) := by
  rw [independent_head_product_volume_density]
  let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
  exact congrArg₂ (fun x y => x*y) (L.head_coefficient_old_labels q δ) (L.head_prepared_old_labels q ε)
end IntegrationInACVF.Section7
