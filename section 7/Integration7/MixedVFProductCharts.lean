module

public import Integration7.PositiveVFVolumeProductMaps
public import Integration7.VFBlockProductJacobians
public import Section9.MixedJacobian

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual fixed-label VF charts on Cartesian product maps, with one
common radius controlling the two original coordinate blocks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}
variable {U U' : PositiveVFVolumeObject (M := M) S n} {V V' : PositiveVFVolumeObject (M := M) S m}

theorem positive_vf_volume_product_map_pair
    (f : Map U.domain U'.domain) (g : Map V.domain V'.domain) (u : U.domain) (v : V.domain) :
    positiveVFVolumeProductMap f g ((mixedPack U.domain V.domain).toImage ⟨(u.val,v.val),u.property,v.property⟩) =
      (mixedPack U'.domain V'.domain).toImage ⟨((f u).val,(g v).val),(f u).property,(g v).property⟩ := by
  unfold positiveVFVolumeProductMap
  simp only [Map.comp_apply,mixedUnpack_pack]
  rfl

theorem is_vf_chart_at_product
    (f : Map U.domain U'.domain) (g : Map V.domain V'.domain) (u : U.domain) (v : V.domain)
    (F : (Fin (n+1) → VFType (M := M)) → Fin (n+1) → VFType (M := M))
    (G : (Fin (m+1) → VFType (M := M)) → Fin (m+1) → VFType (M := M))
    (hF : IsVFChartAt f u F) (hG : IsVFChartAt g v G) :
    IsVFChartAt (positiveVFVolumeProductMap f g)
      ((mixedPack U.domain V.domain).toImage ⟨(u.val,v.val),u.property,v.property⟩) (tupleBlockProduct (n := n+1) (m := m+1) F G) := by
  obtain ⟨ρF,hρF⟩ := hF
  obtain ⟨ρG,hρG⟩ := hG
  refine ⟨max ρF ρG,?_⟩
  intro x hx
  change x ∈ vfBall (Fin.append u.val.1 v.val.1) (max ρF ρG) at hx
  let xl : Fin (n+1) → VFType (M := M) := fun i => x (Fin.castAdd (m+1) i)
  let xr : Fin (m+1) → VFType (M := M) := fun i => x (Fin.natAdd (n+1) i)
  have hBallF : xl ∈ vfBall u.val.1 ρF := by
    intro i
    apply lt_of_le_of_lt (show ρF.val ≤ (max ρF ρG).val from le_max_left _ _)
    simpa only [Fin.append_left] using hx (Fin.castAdd (m+1) i)
  have hBallG : xr ∈ vfBall v.val.1 ρG := by
    intro i
    apply lt_of_le_of_lt (show ρG.val ≤ (max ρF ρG).val from le_max_right _ _)
    simpa only [Fin.append_right] using hx (Fin.natAdd (n+1) i)
  obtain ⟨hu,hfu⟩ := hρF xl hBallF
  obtain ⟨hv,hgv⟩ := hρG xr hBallG
  let a : U.domain := ⟨(xl,u.val.2),hu⟩
  let b : V.domain := ⟨(xr,v.val.2),hv⟩
  let w := (mixedPack U.domain V.domain).toImage ⟨(a.val,b.val),a.property,b.property⟩
  have hw : w.val = (x,Fin.append u.val.2 v.val.2) :=
    Prod.ext Fin.append_castAdd_natAdd rfl
  have hmem : (x,Fin.append u.val.2 v.val.2) ∈ (U.prod V).domain.carrier := hw ▸ w.property
  refine ⟨hmem,?_⟩
  change (positiveVFVolumeProductMap f g ⟨(x,Fin.append u.val.2 v.val.2),hmem⟩).val =
    (tupleBlockProduct (n := n+1) (m := m+1) F G x,
      (positiveVFVolumeProductMap f g ((mixedPack U.domain V.domain).toImage
        ⟨(u.val,v.val),u.property,v.property⟩)).val.2)
  have hpoint : (⟨(x,Fin.append u.val.2 v.val.2),hmem⟩ : (U.prod V).domain) = w := Subtype.ext hw.symm
  rw [hpoint]
  dsimp only [w]
  rw [positive_vf_volume_product_map_pair,positive_vf_volume_product_map_pair]
  change (Fin.append (f a).val.1 (g b).val.1,Fin.append (f a).val.2 (g b).val.2) =
    (Fin.append (F xl) (G xr),Fin.append (f u).val.2 (g v).val.2)
  have hF1 := congrArg Prod.fst hfu
  have hG1 := congrArg Prod.fst hgv
  have hF2 := congrArg Prod.snd hfu
  have hG2 := congrArg Prod.snd hgv
  exact Prod.ext (congrArg₂ Fin.append hF1 hG1) (congrArg₂ Fin.append hF2 hG2)

end IntegrationInACVF.Section7
