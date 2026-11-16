module

public import Integration7.VolumeBlowupCoordinatePermutations
public import Integration7.VolumeBlowupRightProducts
public import Integration7.GammaVolumeSliceDensityAssembly
public import IntegrationSection6.GammaSwappedVolumes

@[expose] public section

/-! Swapping a unary VF volume block with the selected RV block
preserves common volume blowups. Both densities remain unchanged;
the determinant signs cancel by simultaneous rescaling. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section7 (gammaVolumeValue)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

private theorem unary_swap_degree (k : ℕ) : k+1 = 1+k := by omega

private def unarySwapPermutation (k : ℕ) : Equiv.Perm (Fin ((k+1)+1)) :=
  (finAddFlip : Fin ((k+1)+1) ≃ Fin (1+(k+1))).trans
    (finCongr (congrArg Nat.succ (unary_swap_degree k))).symm

private theorem swap_chart
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : GammaRVFiniteObject B (1+(k+1))) (hUC : U.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object))
    (hδ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero) :
    let A := (gammaCoordinateDensityObject (e := 1) (k := k) hc C U hUC δ hδ).reindexDegree (unary_swap_degree k)
    let V := gammaCoordinateDensityObject (e := k+1) (k := 0) hc C (gammaSwapVolumeBlocks U) hUC δ hδ
    ∃ f : A.underlying ≅ V.underlying,
      (∀ u, V.underlying.obj.value (finiteIsoMap f u) = A.underlying.obj.value u ∘ unarySwapPermutation k) ∧
      (∀ u, V.form.value (finiteIsoMap f u) = A.form.value u) := by
  intro A V
  let f : Map A.underlying.obj.domain V.underlying.obj.domain := Map.inclusion (fun _ h => h)
  have hf : Function.Bijective f := ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
    fun v => ⟨⟨v.val,v.property⟩,rfl⟩⟩
  have hcoord : ∀ u, V.underlying.obj.value (f u) = A.underlying.obj.value u ∘ unarySwapPermutation k := by
    intro u
    change (gammaVolumeValue U.toGammaRVObject ⟨u.val,u.property⟩ ∘ finAddFlip) =
      (gammaVolumeValue U.toGammaRVObject ⟨u.val,u.property⟩ ∘
        finCongr (congrArg Nat.succ (unary_swap_degree k))) ∘ unarySwapPermutation k
    funext i
    simp only [Function.comp_apply,unarySwapPermutation,Equiv.trans_apply]
    exact congrArg (gammaVolumeValue U.toGammaRVObject ⟨u.val,u.property⟩)
      ((finCongr (congrArg Nat.succ (unary_swap_degree k))).apply_symm_apply (finAddFlip i)).symm
  exact ⟨rvFiniteIsoOfAmbient (rvIsoOfLabelEquiv f hf
    (rvReindexEquiv (unarySwapPermutation k)) (rvWeight_reindex _) hcoord),hcoord,fun _ => rfl⟩

theorem gamma_unary_volume_block_swap_common
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : GammaRVFiniteObject B (1+(k+1)))
    (hUC : U.codes ⊆ (C.base : Set M)) (hVC : V.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object)) (ε : Fin (rvObjectArity V.object))
    (hδ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (hε : ∀ v : rvObjectDomain V.object, (v.val ε).val ≠ iRVZero)
    (h : VolumeBlowupEquivalent (gammaCoordinateDensityObject (e := 1) (k := k) hc C U hUC δ hδ)
      (gammaCoordinateDensityObject (e := 1) (k := k) hc C V hVC ε hε)) :
    VolumeBlowupEquivalent
      (gammaCoordinateDensityObject (e := k+1) (k := 0) hc C (gammaSwapVolumeBlocks U) hUC δ hδ)
      (gammaCoordinateDensityObject (e := k+1) (k := 0) hc C (gammaSwapVolumeBlocks V) hVC ε hε) := by
  obtain ⟨fU,hU,hφU⟩ := swap_chart hc C U hUC δ hδ
  obtain ⟨fV,hV,hφV⟩ := swap_chart hc C V hVC ε hε
  exact (h.reindexDegree hc C (unary_swap_degree k)).of_permuted_coordinate_charts hc C
    (unarySwapPermutation k) fU fV hU hV hφU hφV

end IntegrationInACVF.Section7
