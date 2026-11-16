module

public import Integration7.LowerDimensionRVVolumeIsomorphisms
public import Integration7.RVVolumeComposition
public import Integration7.RVVolumeInverse
public import Integration7.GammaRVMapGraphOperations
public import Integration7.GammaVolumeIsoGraphOperations

@[expose] public section

/-! Volume isomorphisms on smaller-dimensional RV domains compose and
invert in the given real presentation. Their RV Jacobian conditions are
vacuous there; their pointwise Gamma equations are still proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def RVVolumeIso.transOfSmallDimension {U V W : PositiveRVVolumeObject (M := M) S k}
    (f : RVVolumeIso U V) (g : RVVolumeIso V W) (hd : rvDim U.essential.obj.domain < k+1) : RVVolumeIso U W := by
  apply RVVolumeIso.of_absoluteRatio_of_lower_rvDim (f.iso.trans g.iso) hd
  intro u
  have hv : (∏ i, RVOperations.absoluteHom (V.essential.obj.value (finiteIsoMap f.iso u) i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (RVOperations.absolute_eq_zero _).not.mpr
      ((rv_nonzero_iff_raw _).mpr (V.essential_nonzero (finiteIsoMap f.iso u) i)))
  rw [volumeRatio_trans,map_mul,g.absolute_volumeRatio,f.absolute_volumeRatio,div_mul_div_comm,
    mul_comm (∏ i, RVOperations.absoluteHom (W.essential.obj.value (finiteIsoMap g.iso (finiteIsoMap f.iso u)) i))
      (∏ i, RVOperations.absoluteHom (V.essential.obj.value (finiteIsoMap f.iso u) i)),mul_div_mul_left _ _ hv]
  rw [finiteIsoMap_trans]

def RVVolumeIso.symmOfSmallDimension {U V : PositiveRVVolumeObject (M := M) S k}
    (f : RVVolumeIso U V) (hd : rvDim V.essential.obj.domain < k+1) : RVVolumeIso V U := by
  apply RVVolumeIso.of_absoluteRatio_of_lower_rvDim f.iso.symm hd
  intro v
  have h := congrArg Inv.inv (f.absolute_volumeRatio (finiteIsoMap f.iso.symm v))
  simpa only [volumeRatio_symm,map_inv₀,inv_div,finiteIsoMap_apply_symm] using h

theorem RVVolumeIso.GammaDefinable.transOfSmallDimension {B : Base (M := M)}
    {U V W : PositiveRVVolumeObject (M := M) S k} {f : RVVolumeIso U V} {g : RVVolumeIso V W}
    (hf : f.GammaDefinable B) (hg : g.GammaDefinable B) (hd : rvDim U.essential.obj.domain < k+1) :
    (f.transOfSmallDimension g hd).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((SpecialTransformations.Section5.gammaLogicInput B).comp_graph hf hg)
  intro p q
  constructor
  · rintro ⟨m,⟨u,hu,hm⟩,⟨v,hv,hq⟩⟩
    have he : v = finiteIsoMap f.iso u := Subtype.ext (hv.trans hm.symm)
    exact ⟨u,hu,(congrArg (fun z => (finiteIsoMap g.iso z).val) he).symm.trans hq⟩
  · rintro ⟨u,hu,hq⟩
    exact ⟨(Fin.elim0,(finiteIsoMap f.iso u).val),⟨u,hu,rfl⟩,⟨finiteIsoMap f.iso u,rfl,hq⟩⟩

theorem RVVolumeIso.GammaDefinable.symmOfSmallDimension {B : Base (M := M)}
    {U V : PositiveRVVolumeObject (M := M) S k} {f : RVVolumeIso U V}
    (hf : f.GammaDefinable B) (hd : rvDim V.essential.obj.domain < k+1) :
    (f.symmOfSmallDimension hd).GammaDefinable B := by
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr
    ((SpecialTransformations.Section5.gammaLogicInput B).swap_graph hf)
  intro p q
  constructor
  · rintro ⟨u,hu,hp⟩
    exact ⟨finiteIsoMap f.iso u,hp,(congrArg (fun z : U.essential.obj.domain => z.val)
      (finiteIsoMap_symm_apply f.iso u)).trans hu⟩
  · rintro ⟨v,hv,hq⟩
    exact ⟨finiteIsoMap f.iso.symm v,hq,(congrArg (fun z : V.essential.obj.domain => z.val)
      (finiteIsoMap_apply_symm f.iso v)).trans hv⟩

end IntegrationInACVF.Section7
