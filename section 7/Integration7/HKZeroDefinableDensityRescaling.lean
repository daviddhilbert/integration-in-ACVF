import Integration7.HKZeroVolumeParameterDescent
import Integration7.DefinableDensityRescaling

/-! Exact weighted-zero isomorphisms retain their density equation after
base extension or multiplication by a common definable nonzero scalar. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M}

def ZeroRVVolumeIso.extend {U V : ZeroRVVolumeObject (M := M) S}
    (e : ZeroRVVolumeIso U V) (hST : S ⊆ T) : ZeroRVVolumeIso (U.extend hST) (V.extend hST) :=
  ⟨finiteVolumeIsoExtend hST e.iso,fun u => e.density ⟨u.val,u.property⟩⟩

def ZeroRVVolumeObject.rescaleDefinable (U : ZeroRVVolumeObject (M := M) S)
    (c : CanonicalRV.RVSort M) (hc : S.Definable₁ LRV {c.val}) (h0 : c ≠ 0) : ZeroRVVolumeObject (M := M) S :=
  ⟨U.underlying,U.form.rescaleDefinable c hc h0⟩

def ZeroRVVolumeIso.rescaleDefinable {U V : ZeroRVVolumeObject (M := M) S}
    (e : ZeroRVVolumeIso U V) (c : CanonicalRV.RVSort M)
    (hc : S.Definable₁ LRV {c.val}) (h0 : c ≠ 0) :
    ZeroRVVolumeIso (U.rescaleDefinable c hc h0) (V.rescaleDefinable c hc h0) :=
  ⟨e.iso,fun u => congrArg (fun z => c*z) (e.density u)⟩

end IntegrationInACVF.Section7.HK
