module

public import IntegrationSection6.MixedVFFibreCompactness

@[expose] public section

/-! Point functions survive the existing point/sorted and carrier-equality
adapters. These identities retain graph constraints during uniformization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {r s n a m b : ℕ}

theorem sorted_iso_congr_value {sr : Fin r → SortTag} {ss : Fin s → SortTag}
    {D D' : Set (Fin r → M)} {E E' : Set (Fin s → M)}
    (e : GammaSortedIso B sr ss D E) (hD : D = D') (hE : E = E') (x : D') :
    ((e.congr hD hE).equiv x).val =
      (e.equiv ⟨x.val,(Set.ext_iff.mp hD x.val).mpr x.property⟩).val := by
  cases hD
  cases hE
  rfl

theorem point_iso_sorted_code {A : Set (Point (M := M) n a)} {D : Set (Point (M := M) m b)}
    (e : GammaIso B A D) (x : A) :
    ((GammaIso.toSortedIso e).equiv (pointSetCodeEquiv A x)).val = gammaPointCode (e.equiv x).val := by
  change gammaPointCode (e.equiv ((pointSetCodeEquiv A).symm ((pointSetCodeEquiv A) x))).val = _
  rw [Equiv.symm_apply_apply]

end IntegrationInACVF.Section7.HK
