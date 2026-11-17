module

public import Integration7.RawStandardVolumeObjects
public import Integration7.VolumeRelabeling
public import Section4.RVIsoTools

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! With no old selected coordinates a unary selected object is the
actual raw contraction object, including its retained density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a : ℕ}

def unaryRawSelectedVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a)
    (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (T : StandardContraction A (Equiv.refl _)) :
    RVVolumeIso
      (selectedStandardVolumeObject hc C Ξ A (Fin.elim0 : Fin 0 → Fin a) δ hδ
        (fun x _ => (hfin x).subset (fun _ h => h.1)) T)
      (rawStandardVolumeObject hc C Ξ A hfin δ hδ T) := by
  let U := selectedStandardVolumeObject hc C Ξ A (Fin.elim0 : Fin 0 → Fin a) δ hδ
    (fun x _ => (hfin x).subset (fun _ h => h.1)) T
  let V := rawStandardVolumeObject hc C Ξ A hfin δ hδ T
  have hUV : U.underlying.obj.domain.carrier = V.underlying.obj.domain.carrier := by
    ext r
    exact (mem_rawVolumeContractionLabels hc T.target r).trans (rawContractionDomain_iff T (Fin.elim0,r)).symm
  have hCoord (u : U.underlying.obj.domain) :
      V.underlying.obj.value ⟨u.val,hUV.le u.property⟩ = U.underlying.obj.value u := by
    funext i
    have hi : i=0 := Fin.ext (by omega)
    subst i
    rfl
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := V.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain
      U.underlying.obj.volume V.underlying.obj.volume hUV hCoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc C e hCoord (fun _ => rfl)
end IntegrationInACVF.Section7
