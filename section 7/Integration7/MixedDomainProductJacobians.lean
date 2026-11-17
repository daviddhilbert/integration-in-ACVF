module

public import Section4.MixedProducts
public import Section4.ProductBijections
public import Integration7.VFBlockProductJacobians
public import Section9.MixedJacobian

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual Cartesian product maps and fixed-label Jacobians in arbitrary
VF arities, including products with a genuine degree-zero lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m a a' b b' : ℕ}
variable {U : DefSet (rawMixedSpace (M := M) n a) S} {U' : DefSet (rawMixedSpace (M := M) n a') S}
variable {V : DefSet (rawMixedSpace (M := M) m b) S} {V' : DefSet (rawMixedSpace (M := M) m b') S}

def mixedDomainProductMap (f : Map U U') (g : Map V V') :
    Map (mixedProductDomain U V) (mixedProductDomain U' V') :=
  (mixedPack U' V').toImage.comp ((Map.prodMap f g).comp (mixedUnpack U V))

theorem mixed_domain_product_map_bijective (f : Map U U') (g : Map V V')
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (mixedDomainProductMap f g) :=
  (mixedPackToImage_bijective U' V').comp
    ((Map.prodMap_bijective f g hf hg).comp
      ⟨fun p q h => by
        have he := congrArg (mixedPack U V).toImage h
        simpa only [mixedPack_unpack] using he,
       fun p => ⟨(mixedPack U V).toImage p,mixedUnpack_pack U V p⟩⟩)


theorem mixed_domain_product_map_pair
    (f : Map U U') (g : Map V V') (u : U) (v : V) :
    mixedDomainProductMap f g ((mixedPack U V).toImage ⟨(u.val,v.val),u.property,v.property⟩) =
      (mixedPack U' V').toImage ⟨((f u).val,(g v).val),(f u).property,(g v).property⟩ := by
  unfold mixedDomainProductMap
  simp only [Map.comp_apply,mixedUnpack_pack]
  rfl

theorem is_vf_chart_at_mixed_domain_product
    (f : Map U U') (g : Map V V') (u : U) (v : V)
    (F : (Fin n → VFType (M := M)) → Fin n → VFType (M := M))
    (G : (Fin m → VFType (M := M)) → Fin m → VFType (M := M))
    (hF : IsVFChartAt f u F) (hG : IsVFChartAt g v G) :
    IsVFChartAt (mixedDomainProductMap f g)
      ((mixedPack U V).toImage ⟨(u.val,v.val),u.property,v.property⟩) (tupleBlockProduct (n := n) (m := m) F G) := by
  obtain ⟨ρF,hρF⟩ := hF
  obtain ⟨ρG,hρG⟩ := hG
  refine ⟨max ρF ρG,?_⟩
  intro x hx
  change x ∈ vfBall (Fin.append u.val.1 v.val.1) (max ρF ρG) at hx
  let xl : Fin n → VFType (M := M) := fun i => x (Fin.castAdd m i)
  let xr : Fin m → VFType (M := M) := fun i => x (Fin.natAdd n i)
  have hBallF : xl ∈ vfBall u.val.1 ρF := by
    intro i
    apply lt_of_le_of_lt (show ρF.val ≤ (max ρF ρG).val from le_max_left _ _)
    simpa only [Fin.append_left] using hx (Fin.castAdd m i)
  have hBallG : xr ∈ vfBall v.val.1 ρG := by
    intro i
    apply lt_of_le_of_lt (show ρG.val ≤ (max ρF ρG).val from le_max_right _ _)
    simpa only [Fin.append_right] using hx (Fin.natAdd n i)
  obtain ⟨hu,hfu⟩ := hρF xl hBallF
  obtain ⟨hv,hgv⟩ := hρG xr hBallG
  let a : U := ⟨(xl,u.val.2),hu⟩
  let b : V := ⟨(xr,v.val.2),hv⟩
  let w := (mixedPack U V).toImage ⟨(a.val,b.val),a.property,b.property⟩
  have hw : w.val = (x,Fin.append u.val.2 v.val.2) :=
    Prod.ext Fin.append_castAdd_natAdd rfl
  have hmem : (x,Fin.append u.val.2 v.val.2) ∈ (mixedProductDomain U V).carrier := hw ▸ w.property
  refine ⟨hmem,?_⟩
  change (mixedDomainProductMap f g ⟨(x,Fin.append u.val.2 v.val.2),hmem⟩).val =
    (tupleBlockProduct (n := n) (m := m) F G x,
      (mixedDomainProductMap f g ((mixedPack U V).toImage
        ⟨(u.val,v.val),u.property,v.property⟩)).val.2)
  have hpoint : (⟨(x,Fin.append u.val.2 v.val.2),hmem⟩ : (mixedProductDomain U V)) = w := Subtype.ext hw.symm
  rw [hpoint]
  dsimp only [w]
  rw [mixed_domain_product_map_pair,mixed_domain_product_map_pair]
  change (Fin.append (f a).val.1 (g b).val.1,Fin.append (f a).val.2 (g b).val.2) =
    (Fin.append (F xl) (G xr),Fin.append (f u).val.2 (g v).val.2)
  have hF1 := congrArg Prod.fst hfu
  have hG1 := congrArg Prod.fst hgv
  have hF2 := congrArg Prod.snd hfu
  have hG2 := congrArg Prod.snd hgv
  exact Prod.ext (congrArg₂ Fin.append hF1 hG1) (congrArg₂ Fin.append hF2 hG2)

theorem has_mixed_vf_jacobian_domain_product
    (f : Map U U') (g : Map V V') (u : U) (v : V)
    (J K : VFType (M := M)) (hf : HasMixedVFJacobianAt f u J) (hg : HasMixedVFJacobianAt g v K) :
    HasMixedVFJacobianAt (mixedDomainProductMap f g)
      ((mixedPack U V).toImage ⟨(u.val,v.val),u.property,v.property⟩) (J*K) := by
  obtain ⟨F,hF,hJF⟩ := hf
  obtain ⟨G,hG,hJG⟩ := hg
  exact ⟨tupleBlockProduct (n := n) (m := m) F G,
    is_vf_chart_at_mixed_domain_product f g u v F G hF hG,
    has_vf_jacobian_block_product F G u.val.1 v.val.1 J K hJF hJG⟩

end IntegrationInACVF.Section7
