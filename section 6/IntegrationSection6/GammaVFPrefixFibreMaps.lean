import IntegrationSection6.GammaVFPrefixFibres
import IntegrationSection6.VFPrefixFibreMaps

/-! Complete original-Gamma graphs for maps and bijections of VF prefix
fibres. Only the frozen complementary VF tuple becomes named. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n p a b : ℕ}
variable {U : DefSet (M := M) S (n+p) a} {V : DefSet (M := M) S (n+p) b}

theorem gamma_vfPrefixFibreMap (f : Map U V) (hF : GammaGraphDefinable B (pointMapGraph f))
    (hi : VFPrefixRelative f) (x : Fin n → VF (M := M)) :
    GammaGraphDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (pointMapGraph (vfPrefixFibreMap f hi x)) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
  have hF' : GammaGraphDefinable C (pointMapGraph f) := hF.mono Set.subset_union_left (Set.Subset.refl _)
  have h := hF'.preimage_maps (vfPrefixInsertMap B.real x p a) (vfPrefixInsertMap B.real x p b)
  apply GammaGraphDefinable.congr h
  intro q r
  constructor
  · rintro ⟨u,hu,hr⟩
    change u.val = vfPrefixInsert x q at hu
    change (f u).val = vfPrefixInsert x r at hr
    have hq : vfPrefixInsert x q ∈ carrier U := hu ▸ u.property
    let v : vfPrefixFibre U x := ⟨q,hq⟩
    refine ⟨v,rfl,?_⟩
    apply vfPrefixInsert_injective x
    rw [vfPrefixFibreMap_insert]
    have he : (⟨vfPrefixInsert x v.val,v.property⟩ : U) = u := Subtype.ext hu.symm
    rw [he]
    exact hr
  · rintro ⟨q,rfl,hr⟩
    refine ⟨⟨vfPrefixInsert x q.val,q.property⟩,rfl,?_⟩
    exact (vfPrefixFibreMap_insert f hi x q).symm.trans (congrArg (vfPrefixInsert x) hr)

def gammaVFPrefixFibreIso (f : Map U V) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f)) (hi : VFPrefixRelative f)
    (x : Fin n → VF (M := M)) :
    GammaIso ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (carrier (vfPrefixFibre U x)) (carrier (vfPrefixFibre V x)) where
  equiv := Equiv.ofBijective (vfPrefixFibreMap f hi x) (vfPrefixFibreMap_bijective f hf hi x)
  graph := gamma_vfPrefixFibreMap f hF hi x

end IntegrationInACVF.Section6
