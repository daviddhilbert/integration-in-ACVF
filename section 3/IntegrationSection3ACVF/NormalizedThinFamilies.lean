import IntegrationSection3ACVF.NormalizedThinGeometry
import IntegrationSection3ACVF.FiniteFamilyMaximal

/-! Normalization of a finite thin family preserves its actual union,
disjointness, number of components and total number of actual holes. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open scoped BigOperators
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry

namespace IntegrationInACVF.Section3ACVF.NormalizedThinFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => @CanonicalStructure.normalize M sM
local notation "hN" => @CanonicalStructure.normalized_model M sM hM

def family (F : Finset (PuncturedBall M)) : Finset (@PuncturedBall M N) :=
  F.map ⟨NormalizedThinGeometry.normalize,NormalizedThinGeometry.normalize_injective⟩

theorem body_family (F : Finset (PuncturedBall M)) : @body M N (family F) = body F := by
  ext x
  constructor
  · rintro ⟨d,hd,hxd⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hd
    exact ⟨a,ha,hxd⟩
  · rintro ⟨d,hd,hxd⟩
    exact ⟨NormalizedThinGeometry.normalize d,Finset.mem_map.mpr ⟨d,hd,rfl⟩,hxd⟩

theorem card_family (F : Finset (PuncturedBall M)) : (family F).card = F.card := Finset.card_map _

theorem holes_family (F : Finset (PuncturedBall M)) :
    (∑ d : family F, (@PuncturedBall.holes M N d.val).card) = ∑ d : F, d.val.holes.card := by
  let E : F ≃ family F := Finset.equivMap
    ⟨NormalizedThinGeometry.normalize,NormalizedThinGeometry.normalize_injective⟩ F
  exact (Fintype.sum_equiv E (fun d : F => d.val.holes.card)
    (fun d : family F => (@PuncturedBall.holes M N d.val).card) (fun d => rfl)).symm

theorem thin_family (F : Finset (PuncturedBall M)) (hThin : ∀ d ∈ F, IsThin d) :
    ∀ d ∈ family F, @IsThin M N hN d := by
  intro d hd
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hd
  exact NormalizedThinGeometry.thin_normalize (hThin a ha)

theorem disjoint_family (F : Finset (PuncturedBall M))
    (hDis : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body)) :
    ((family F : Finset (@PuncturedBall M N)) : Set (@PuncturedBall M N)).Pairwise
      (fun d e => Disjoint (@PuncturedBall.body M N d) (@PuncturedBall.body M N e)) := by
  intro d hd e he hde
  obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hd
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp he
  exact hDis ha hb (fun hab => hde (congrArg NormalizedThinGeometry.normalize hab))

end IntegrationInACVF.Section3ACVF.NormalizedThinFamilies
