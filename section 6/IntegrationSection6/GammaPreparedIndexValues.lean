import IntegrationSection6.GammaPreparedIndexPresentation
import IntegrationSection6.GammaPresentationTotalVolume

/-! Exact prepared-index volumes and recovery of the saturated VF base
from its full RV key set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l : ℕ}

theorem PreparedIndexPresentation.totalVolume_eq (C : DefSet (M := M) S p l)
    (BP : PreparedIndexPresentation B C) (t : Fin (p+l) → RV (M := M)) (ht : t ∈ preparedKeyDomain C) :
    BP.totalVolume t = t ∘ Fin.castAdd l :=
  ((BP.totalVolume_graph t (t ∘ Fin.castAdd l)).mp
    ((BP.graph_iff t (t ∘ Fin.castAdd l)).mpr ⟨ht,ht,rfl⟩)).2

theorem prepared_key_domain_iff (C : DefSet (M := M) S p l)
    (hC : IsRVPullback (carrier C)) (q : Point (M := M) p l) :
    (flatKey q).2 ∈ preparedKeyDomain C ↔ q ∈ carrier C := by
  constructor
  · rintro ⟨x,hx⟩
    have he : flatKey x.val = flatKey q := Prod.ext (Subsingleton.elim _ _) hx
    have hs : SameRV x.val q := (flatKey_eq_iff _ _).mp he
    rw [← hC]
    exact ⟨x.val,x.property,hs⟩
  · intro hq
    exact ⟨⟨q,hq⟩,rfl⟩

end IntegrationInACVF.Section6
