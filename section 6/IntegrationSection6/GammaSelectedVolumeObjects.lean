import IntegrationSection6.GammaAmbientVolumeKeys
import IntegrationSection6.FiniteLiftFibres

/-! Appending selected old RV labels to a volume gives an RV[n+e] object
under exactly relative finite-lift-fibre finiteness. The unaugmented object
need not have finite volume fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n e : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def appendSelectedVolumeObject (U : @RVObject M N S n) (ρ : Fin e → Fin (rvObjectArity U)) :
    @RVObject M N S (n+e) :=
  @RVObject.mk M N S (n+e) (rvObjectArity U) (rvObjectDomain U)
    (@SpecialTransformations.DefinableGeometry.Map.comp LRV M N _ _ _ S _ _ _
      (@rvPack M N S n e
        (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N n) S)
        (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N e) S))
      (@SpecialTransformations.DefinableGeometry.Map.pair LRV M N _ _ _ S _ _ _ (rvObjectVolume U)
        (@selectRVTuple M N S (rvObjectArity U) e ρ (rvObjectDomain U))))

theorem appendSelectedVolumeObject_value (U : @RVObject M N S n)
    (ρ : Fin e → Fin (rvObjectArity U)) (u : rvObjectDomain U) :
    (rvObjectVolume (appendSelectedVolumeObject U ρ) u).val =
      Fin.append (rvObjectVolume U u).val (u.val ∘ ρ) := rfl

theorem appendSelectedVolumeObject_finite (U : @RVObject M N S n)
    (ρ : Fin e → Fin (rvObjectArity U))
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin (rvObjectArity U) → RV (M := M) | (x,r) ∈ carrier (rawLift U) ∧ r ∘ ρ = t}.Finite) :
    Map.FiniteFibres (rvObjectVolume (appendSelectedVolumeObject U ρ)) := by
  intro t
  obtain ⟨x,hx⟩ := @tupleRV_surjective M N hN n (t.val ∘ Fin.castAdd e)
  apply (hfin x (t.val ∘ Fin.natAdd n)).of_injOn (f := fun u : rvObjectDomain U => u.val)
  · intro u hu
    have he := congrArg (fun v => v.val) hu
    rw [appendSelectedVolumeObject_value] at he
    have hHead : (rvObjectVolume U u).val = t.val ∘ Fin.castAdd e := by
      funext j
      exact (Fin.append_left _ _ j).symm.trans (congrFun he (Fin.castAdd e j))
    have hTail : u.val ∘ ρ = t.val ∘ Fin.natAdd n := by
      funext j
      exact (Fin.append_right _ _ j).symm.trans (congrFun he (Fin.natAdd n j))
    exact ⟨⟨u,rfl,hHead.trans hx.symm⟩,hTail⟩
  · intro u hu v hv he
    exact Subtype.ext he

def gammaAppendSelectedVolume (U : GammaRVObject B n) (ρ : Fin e → Fin (rvObjectArity U.object)) :
    GammaRVObject B (n+e) where
  codes := U.codes
  real_contains := U.real_contains
  object := appendSelectedVolumeObject U.object ρ
  domain_graph := U.domain_graph
  volume_graph := by
    let H := @selectRVTuple M N B.real (rvObjectArity U.object) e ρ
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object)) B.real)
    exact gamma_ambient_volume_key_graph U H
      (fun u => (rvObjectVolume (appendSelectedVolumeObject U.object ρ) u).val) (fun _ => rfl)

def gammaFiniteSelectedVolume (U : GammaRVObject B n) (ρ : Fin e → Fin (rvObjectArity U.object))
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin (rvObjectArity U.object) → RV (M := M) | (x,r) ∈ U.lift ∧ r ∘ ρ = t}.Finite) :
    GammaRVFiniteObject B (n+e) :=
  ⟨gammaAppendSelectedVolume U ρ,appendSelectedVolumeObject_finite U.object ρ hfin⟩

end IntegrationInACVF.Section6
