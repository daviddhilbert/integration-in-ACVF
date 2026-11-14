import Integration7.CanonicalVolumeSchemaRows
import Integration7.GammaVolumeIsomorphismSchemata
import Integration7.FiniteVolumeIsoMaps

/-! An actual essential bijection gives ordinary schema validity on its
exact chart. Nonzero coordinates give the weight clause automatically;
the volume equations remain separate obligations. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
variable {U V : PositiveRVVolumeObject (M := M) S k}
variable {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
variable {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp} {z : Fin p → M}
variable {H : Set (Fin ((p+U.underlying.obj.arity)+V.underlying.obj.arity) → M)}

theorem RVVolumeSchemaRow.bijectiveRowValid (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (hz : ∀ i, sortEval (sp i) (z i))
    (e : U.essential ≅ V.essential)
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y) :
    bijectiveMapRowValid sp (fun _ => .rv)
      (essentialFiniteVolumeSchema F.object).domain (essentialFiniteVolumeSchema G.object).domain H z := by
  have hlabel {u u' : U.essential.obj.domain} (h : rvValues u.val = rvValues u'.val) : u = u' :=
    Subtype.ext (rvValues_injective h)
  have hSource (x) (hx : Fin.append z x ∈ (essentialFiniteVolumeSchema F.object).domain) :
      ∃ u : U.essential.obj.domain, rvValues u.val = x := by
    have hxRV (i) : iRV (x i) := by
      simpa only [Fin.append_right,sortEval,iRV] using
        (essentialFiniteVolumeSchema F.object).domain_definable.proper _ hx (Fin.natAdd p i)
    let t : Fin U.underlying.obj.arity → CanonicalRV.RVSort M := fun i => ⟨x i,hxRV i⟩
    exact ⟨⟨t,(P.essential_domain_iff t).mp hx⟩,rfl⟩
  have hTarget (y) (hy : Fin.append z y ∈ (essentialFiniteVolumeSchema G.object).domain) :
      ∃ v : V.essential.obj.domain, rvValues v.val = y := by
    have hyRV (i) : iRV (y i) := by
      simpa only [Fin.append_right,sortEval,iRV] using
        (essentialFiniteVolumeSchema G.object).domain_definable.proper _ hy (Fin.natAdd p i)
    let t : Fin V.underlying.obj.arity → CanonicalRV.RVSort M := fun i => ⟨y i,hyRV i⟩
    exact ⟨⟨t,(Q.essential_domain_iff t).mp hy⟩,rfl⟩
  refine ⟨⟨hz,?_,?_,?_⟩,?_⟩
  · intro x hx
    obtain ⟨u,rfl⟩ := hSource x hx
    refine ⟨rvValues (finiteIsoMap e u).val,(hH _ _).mpr ⟨u,rfl,rfl⟩,?_⟩
    intro y hy
    obtain ⟨u',hu',hy'⟩ := (hH _ _).mp hy
    exact hy'.symm.trans (congrArg (fun u => rvValues (finiteIsoMap e u).val) (hlabel hu'))
  · intro x y hxy
    obtain ⟨u,rfl,_⟩ := (hH _ _).mp hxy
    exact (P.essential_domain_iff u.val).mpr u.property
  · intro y _
    apply Set.encard_le_coe_iff_finite_ncard_le.mp
    apply Set.encard_le_one_iff.mpr
    intro x x' hx hx'
    obtain ⟨u,hu,hy⟩ := (hH x y).mp hx
    obtain ⟨u',hu',hy'⟩ := (hH x' y).mp hx'
    have he : finiteIsoMap e u = finiteIsoMap e u' :=
      Subtype.ext (rvValues_injective (hy.trans hy'.symm))
    exact hu.symm.trans ((congrArg (fun u : U.essential.obj.domain => rvValues u.val)
      (finiteIsoMap_injective e he)).trans hu')
  · intro y
    constructor
    · intro hy
      obtain ⟨v,rfl⟩ := hTarget y hy
      let u := finiteIsoMap e.symm v
      refine ⟨rvValues u.val,(hH _ _).mpr ⟨u,rfl,?_⟩⟩
      rw [show finiteIsoMap e u = v from finiteIsoMap_apply_symm e v]
    · rintro ⟨x,hxy⟩
      obtain ⟨u,_,rfl⟩ := (hH x y).mp hxy
      exact (Q.essential_domain_iff _).mpr (finiteIsoMap e u).property

theorem essentialVolumeChart_weight_valid
    (F : GammaFiniteRVSchema B p a d sp) (G : GammaFiniteRVSchema B p b d sp)
    (H : Set (Fin ((p+a)+b) → M)) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) :
    weightedChartRowValid sp H (essentialFiniteVolumeSchema F).volume
      (essentialFiniteVolumeSchema G).volume z := by
  refine ⟨hz,?_⟩
  intro r _ _ hF hG
  have hu (i) : chartRowU a b d r i ≠ iRVZero := by
    have h := (hF.2 i).2
    simpa only [Function.comp_apply,Fin.append_right] using h
  have hv (i) : chartRowV a b d r i ≠ iRVZero := by
    have h := (hG.2 i).2
    simpa only [Function.comp_apply,Fin.append_right] using h
  unfold rawWeight
  apply Finset.sum_congr rfl
  intro i _
  rw [if_pos (hu i),if_pos (hv i)]

end IntegrationInACVF.Section7
