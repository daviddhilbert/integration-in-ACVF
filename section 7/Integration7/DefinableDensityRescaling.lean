module

public import Integration7.DefinableVolumeParameterDescent
public import Integration7.NamedMapValueDefinability
public import Integration7.VolumeBlowupRescaling

@[expose] public section

/-! A nonzero density multiplier need only be definable over the base;
its value need not already belong to the smaller term-generated base.
The common blowup relation is preserved by this actual rescaling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
local notation "RV" => CanonicalRV.RVSort M

def rvScalarDefinableConstant {P : Space LRV M} (A : DefSet P S)
    (c : RV) (hc : S.Definable₁ LRV {c.val}) :
    Map A (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let F (_ : P.Index → M) (_ : Fin 1) := c.val
  have hF : S.DefinableMap LRV F := fun _ => SpecialTransformations.DefinableConstants.constant hc
  exact Map.ofCodes A (fun _ => fun _ : Fin 1 => c) F hF
    (fun _ => ⟨_,rfl⟩) (fun _ => rvValues_injective
      (rvValues_decode (M := M) (n := 1) ⟨fun _ => c.val,⟨fun _ => c,rfl⟩⟩))

def VolumeForm.rescaleDefinable {P : Space LRV M} {A : DefSet P S} (ω : VolumeForm A)
    (c : RV) (hc : S.Definable₁ LRV {c.val}) (h0 : c ≠ 0) : VolumeForm A where
  map := (rvMultiply S).comp ((rvScalarDefinableConstant A c hc).pair ω.map).toUniv
  nonzero a := mul_ne_zero h0 (ω.nonzero a)

def PositiveRVVolumeObject.rescaleDefinable (U : PositiveRVVolumeObject (M := M) S k)
    (c : RV) (hc : S.Definable₁ LRV {c.val}) (h0 : c ≠ 0) : PositiveRVVolumeObject (M := M) S k where
  underlying := U.underlying
  form := U.form.rescaleDefinable c hc h0

theorem positive_rescale_definable_density (U : PositiveRVVolumeObject (M := M) S k)
    (c : RV) (hc : S.Definable₁ LRV {c.val}) (h0 : c ≠ 0)
    (u : (U.rescaleDefinable c hc h0).underlying.obj.domain) :
    (U.rescaleDefinable c hc h0).form.value u = c * U.form.value u := rfl

theorem VolumeBlowupEquivalent.rescale_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (c : RV)
    (hDef : (C.base : Set M).Definable₁ LRV {c.val}) (h0 : c ≠ 0) :
    VolumeBlowupEquivalent (U.rescaleDefinable c hDef h0) (V.rescaleDefinable c hDef h0) := by
  let D := finiteVolumeParameterContext C {c.val} (Set.finite_singleton _)
  have hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    fun _ h => finiteVolumeParameterContext_contains C {c.val} _ (Or.inl h)
  have hDc : c.val ∈ D.base := finiteVolumeParameterContext_contains C {c.val} _ (Or.inr rfl)
  have hD : ∀ d ∈ (D.base : Set M), (C.base : Set M).Definable₁ LRV {d} :=
    finite_volume_parameter_context_definable C _ _ (by rintro d rfl; exact hDef)
  exact VolumeBlowupEquivalent.descend_definable hc C D hCD hD
    ((h.extend hCD).rescale hc D c hDc h0)

end IntegrationInACVF.Section7
