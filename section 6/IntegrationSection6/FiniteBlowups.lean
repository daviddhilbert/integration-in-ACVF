import IntegrationSection6.Blowups

/-! The finite-volume restrictions in Remark 6.2 for general and iterated blowups. -/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ} {U V : RVObject (M := M) S k}

/-- An injective RV morphism into a finite-volume object has finite volume.
Both the finite label-image condition and the underlying injectivity are used. -/
theorem finite_volume_of_injective_hom (f : RVHom U V) (hf : Function.Injective f.map)
    (hV : V.volume.FiniteFibres) : U.volume.FiniteFibres := by
  intro t
  have hF (s : Fin k → CanonicalRV.RVSort M) : {v : V.domain | V.value v = s}.Finite := by
    apply (hV ⟨s, Set.mem_univ _⟩).subset
    intro v hv
    exact Subtype.ext hv
  have hB := (f.finite_volume_images t.val).biUnion (fun s _ => hF s)
  apply hB.of_injOn (f := f.map)
  · intro u hu
    refine Set.mem_iUnion.mpr ⟨V.value (f.map u), Set.mem_iUnion.mpr ⟨?_, rfl⟩⟩
    exact ⟨u, congrArg Subtype.val hu, rfl⟩
  · exact hf.injOn

/-- Finite volume is invariant under arbitrary RV isomorphisms. -/
theorem finite_volume_iso (e : U ≅ V) : U.volume.FiniteFibres ↔ V.volume.FiniteFibres :=
  ⟨fun h => finite_volume_of_injective_hom e.inv (iso_map_bijective e.symm).1 h,
    fun h => finite_volume_of_injective_hom e.hom (iso_map_bijective e).1 h⟩

/-- Remark 6.2 for general blowups, including arbitrary elementary charts. -/
theorem Blowup.finite_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (h : Blowup U V) (hU : U.volume.FiniteFibres) : V.volume.FiniteFibres := by
  have hc : h.center.volume.FiniteFibres := (finite_volume_iso h.chart).mpr
    (U.restrict_finite_volume hU h.locus h.contained)
  have he := elementary_finite_volume hκ hs hsmall h.center h.coordinate h.admissible hc
  have hr := U.restrict_finite_volume hU (complement U h.locus)
    (complement_subset U h.locus)
  exact (finite_volume_iso h.result).mpr (rvCoprod_finite_volume _ _ he hr)

/-- Remark 6.2 for the full finite forward iteration. -/
theorem IteratedBlowup.finite_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (h : IteratedBlowup n U V) (hU : U.volume.FiniteFibres) :
    V.volume.FiniteFibres := by
  induction h with
  | zero he =>
    obtain ⟨e⟩ := he
    exact (finite_volume_iso e).mp hU
  | cons h _ ih => exact ih (h.finite_volume hκ hs hsmall hU)

/-- The finite-volume form of Definition 6.7, obtained by restriction of
its genuine common-forward-blowup relation. -/
def finiteIsp (U V : RVFiniteObject (M := M) S k) : Prop := Isp U.obj V.obj

/-- Every intermediate and final witness of the restricted relation remains
finite-volume. This is proved, rather than added to the iteration definition. -/
theorem finiteIsp_witnesses {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U V : RVFiniteObject (M := M) S k} (h : finiteIsp U V) :
    ∃ (m n : ℕ) (A B : RVObject (M := M) S k),
      IteratedBlowup m U.obj A ∧ IteratedBlowup n V.obj B ∧
      A.volume.FiniteFibres ∧ B.volume.FiniteFibres ∧ Nonempty (A ≅ B) := by
  obtain ⟨m, n, A, B, hu, hv, he⟩ := h
  exact ⟨m, n, A, B, hu, hv, hu.finite_volume hκ hs hsmall U.property,
    hv.finite_volume hκ hs hsmall V.property, he⟩

end IntegrationInACVF.Section6
