import Integration7.GammaNamedSection7Results
import Integration7.CanonicalVolumeFamilyIntegrals
import Integration7.SelectedDensityGraphRowMaps
import IntegrationSection6.GammaVFPrefixFibres

/-! Gamma-named function presentations. A selected VF volume family coded
over a context `C` is Gamma over a base `G` when its domain and density graph
are Gamma-definable over `G`. Its row at a VF point `x` is then a Gamma volume
object over `G` with the names of `x` added. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {G : Base (M := M)}
variable {n a k : ℕ}

/-- The Gamma base of a row: `G` with the names of the VF point `x` added. -/
abbrev rowGammaBase (G : Base (M := M)) {n : ℕ} (x : Fin n → VFType (M := M)) : Base (M := M) :=
  ⟨G.real ∪ Set.range (fun j => (x j).val),G.gamma⟩

/-- Gamma certificate of a selected VF volume family. -/
structure SelectedVFVolumeFamily.Gamma (F : SelectedVFVolumeFamily C n a k) (G : Base (M := M)) : Prop where
  domain : GammaSetDefinable G F.domain.carrier
  densityGraph : GammaSetDefinable G (volumeDensityGraph F.form).carrier

theorem vfPrefixTuple_zero (x : Fin n → VFType (M := M)) (y : Fin 0 → VFType (M := M)) :
    vfPrefixTuple x y = x := by
  funext j
  simp only [vfPrefixTuple]
  rw [dif_neg (Nat.not_lt_zero _)]
  exact congrArg x (Fin.ext (Nat.sub_zero _))

theorem gamma_vf_fibre {m : ℕ} {A : Set (Point (M := M) n m)} (hA : GammaSetDefinable G A)
    (x : Fin n → VFType (M := M)) :
    GammaSetDefinable (rowGammaBase G x) {q : Point (M := M) 0 m | (x,q.2) ∈ A} := by
  have h := gamma_vfPrefix_preimage (p := 0) hA x
  convert h using 1
  ext q
  change (x,q.2) ∈ A ↔ (vfPrefixTuple x q.1,q.2) ∈ A
  rw [vfPrefixTuple_zero]

theorem SelectedVFVolumeFamily.Gamma.row_domain {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G)
    (x : Fin n → VFType (M := M)) :
    GammaSetDefinable (rowGammaBase G x) {p : Point (M := M) 0 a |
      p.2 ∈ (F.rowInContext x).underlying.obj.domain.carrier} :=
  gamma_vf_fibre hF.domain x

theorem SelectedVFVolumeFamily.Gamma.row (hc : CanonicalStructure.IsCanonical (M := M))
    {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G) (x : Fin n → VFType (M := M)) :
    VolumeObjectGamma (F.rowInContext x) (rowGammaBase G x) := by
  let Bx := rowGammaBase G x
  have hD := hF.row_domain x
  refine ⟨gamma_rv_coordinate_map hc _ F.selected hD (fun _ => rfl),?_⟩
  have hS := gamma_vf_fibre hF.densityGraph x
  let L := gammaLogicInput Bx
  have h := L.comp_graph (L.swap_graph (L.restrict_graph hS (gamma_drop_last_rv_graph (G := Bx) (n := 0) (a := a))))
    (gamma_last_rv_graph (G := Bx) (n := 0) (a := a))
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨s,⟨hs,rfl⟩,rfl⟩
    obtain ⟨h0,hse⟩ := (mem_volumeDensityGraph_iff F.form (x,s.2)).mp hs
    refine ⟨⟨s.2 ∘ Fin.castAdd 1,h0⟩,rfl,?_⟩
    have hl := congrArg (fun z : Point (M := M) n (a+1) => z.2 (Fin.last a)) hse
    change s.2 (Fin.last a) = Fin.append _ (F.form.map ⟨_,h0⟩).val (Fin.natAdd a (0 : Fin 1)) at hl
    rw [Fin.append_right] at hl
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact hl.symm
  · rintro ⟨u,hu,hq⟩
    refine ⟨(Fin.elim0,Fin.append p.2 q.2),⟨?_,?_⟩,?_⟩
    · change (x,Fin.append p.2 q.2) ∈ (volumeDensityGraph F.form).carrier
      apply (mem_volumeDensityGraph_iff F.form _).mpr
      have hmem : (x,Fin.append p.2 q.2 ∘ Fin.castAdd 1) ∈ F.domain.carrier := by
        have : Fin.append p.2 q.2 ∘ Fin.castAdd 1 = p.2 := by
          funext j
          exact Fin.append_left _ _ j
        rw [this,← hu]
        exact u.property
      refine ⟨hmem,?_⟩
      rw [appendDensityMap_value]
      refine Prod.ext rfl ?_
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp only [Fin.append_left,Function.comp_apply]
      · have hu' : (⟨(x,Fin.append p.2 q.2 ∘ Fin.castAdd 1),hmem⟩ : F.domain) = ⟨(x,u.val),u.property⟩ := by
          apply Subtype.ext
          refine Prod.ext rfl ?_
          change Fin.append p.2 q.2 ∘ Fin.castAdd 1 = u.val
          rw [hu]
          funext j
          exact Fin.append_left _ _ j
        change Fin.append p.2 q.2 (Fin.natAdd a i) =
          Fin.append (Fin.append p.2 q.2 ∘ Fin.castAdd 1) (F.form.map ⟨_,hmem⟩).val (Fin.natAdd a i)
        rw [Fin.append_right,Fin.append_right]
        refine (congrFun hq i).symm.trans ?_
        rw [hu']
        rfl
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext j
      exact (Fin.append_left _ _ j).symm
    · refine Prod.ext (funext (fun i => Fin.elim0 i)) ?_
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact (Fin.append_right _ _ 0).symm

end IntegrationInACVF.Section7
