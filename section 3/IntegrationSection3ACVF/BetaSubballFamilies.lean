import IntegrationSection3ACVF.MaximalSubballFamilies
import IntegrationSection3ACVF.GammaCosetGeometry
import IntegrationSection3.QuotientCover

/-! Infinite actual families of fixed-radius open subballs. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity

namespace IntegrationInACVF.Section3ACVF.BetaSubballFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_subball_subset (a x : VFType (M := M))
    (α β : Values.Gamma (M := M)) (hαβ : α ≤ β)
    (hx : x.val ∈ gammaBall a α true) : gammaBall x β true ⊆ gammaBall a α true := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  obtain ⟨s,hs⟩ := GammaCosetGeometry.vf_representative β
  have hsr := BallEnlargementGeometry.valuation_le_of_gamma_le v hv r s hr hs hαβ
  have hxa := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr x).mp hx
  intro z hz
  let z' : VFType (M := M) := ⟨z,hz.1⟩
  have hzx := (GammaCosetGeometry.gammaBall_mem_valuation v hv x s β hs z').mp hz
  apply (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr z').mpr
  have he : z'-a = (z'-x)+(x-a) := by ring
  rw [he]
  exact lt_of_le_of_lt (v.map_add _ _) (max_lt (lt_of_lt_of_le hzx hsr) hxa)

def family (H : AddSubgroup (VFType (M := M))) (A : Set M) : Set (BallImaginaries.Ball M) :=
  cosetFamily H ∩ {i | BallImaginaries.underlying i ⊆ A}

theorem definable (B : FullBaseAtomicity.Base (M := M))
    (H : AddSubgroup (VFType (M := M)))
    (hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))})
    {A : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A}) :
    FullBaseAtomicity.Family B (family H A) := by
  have h1 := FullBallCoset.cosetFamily_definable B H hH
  have h2 := MaximalSubballFamilies.contained_family_definable B hA
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  letI := CanonicalStructure.normalize (M := M)
  exact ImaginaryBaseFamilies.Family.inter hp h1 h2

theorem member_presentation (H : AddSubgroup (VFType (M := M)))
    (β : Values.Gamma (M := M))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a β true)
    {A : Set M} {i : BallImaginaries.Ball M} (hi : i ∈ family H A) :
    ∃ c : VFType (M := M), BallImaginaries.underlying i = gammaBall c β true := by
  obtain ⟨c,hc,he⟩ := hi.1
  let c' : VFType (M := M) := ⟨c,hc⟩
  exact ⟨c',he.trans ((cosetRelation_fibre H c').trans (hH c'))⟩

theorem cover (H : AddSubgroup (VFType (M := M)))
    (β : Values.Gamma (M := M))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a β true)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (hαβ : α ≤ β) :
    ∀ x ∈ gammaBall a α true, ∃ i ∈ family H (gammaBall a α true),
      x ∈ BallImaginaries.underlying i := by
  intro x hx
  let x' : VFType (M := M) := ⟨x,hx.1⟩
  obtain ⟨i,hi⟩ := GammaCosetGeometry.gammaBall_coded x' β
  refine ⟨i,⟨?_,?_⟩,?_⟩
  · exact ⟨x,x'.property,hi.trans ((hH x').symm.trans (cosetRelation_fibre H x').symm)⟩
  · change BallImaginaries.underlying i ⊆ gammaBall a α true
    rw [hi]
    exact gamma_subball_subset a x' α β hαβ hx
  · rw [hi]
    exact BallEnlargementGeometry.gammaBall_centre_mem x' β true

theorem infinite (h00 : M ⊨ Axioms.ACVF00)
    (H : AddSubgroup (VFType (M := M)))
    (β : Values.Gamma (M := M))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a β true)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (hαβ : α < β) :
    (family H (gammaBall a α true)).Infinite := by
  intro hFin
  apply GammaCosetGeometry.infinite_gamma_cosets h00 H β hH a α hαβ
  apply QuotientCover.image_finite_of_finite_cover (QuotientAddGroup.mk' H) hFin
    (fun i => {x : VFType (M := M) | x.val ∈ BallImaginaries.underlying i})
  · intro i hi x hx y hy
    obtain ⟨c,hc,he⟩ := hi.1
    let c' : VFType (M := M) := ⟨c,hc⟩
    have he' := he.trans (cosetRelation_fibre H c')
    rw [he'] at hx hy
    exact ((GammaCosetGeometry.cosetBody_mem H x c').mp hx).trans
      ((GammaCosetGeometry.cosetBody_mem H y c').mp hy).symm
  · intro x hx
    exact cover H β hH a α hαβ.le x.val hx

theorem disjoint (H : AddSubgroup (VFType (M := M))) (A : Set M) :
    (family H A).Pairwise fun i j => Disjoint (BallImaginaries.underlying i)
      (BallImaginaries.underlying j) := by
  intro i hi j hj hne
  exact cosetFamily_disjoint H hi.1 hj.1 hne

end IntegrationInACVF.Section3ACVF.BetaSubballFamilies
