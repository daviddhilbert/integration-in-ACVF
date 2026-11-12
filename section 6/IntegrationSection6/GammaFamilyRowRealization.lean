import IntegrationSection6.GammaFamilyRawRows
import IntegrationSection6.GammaTupleRelationSpecialization

/-! Actual finite rows of a uniform Gamma family have native finite
presentations and a valid bounded schema using those same global formulas. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

theorem GammaRVFamilyFormula.row_domain_definable (F : GammaRVFamilyFormula B p a k)
    (z : Fin p → VF (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩
      {x : Point (M := M) 0 a | x.2 ∈ F.rowDomain z} := by
  have hD := gamma_tuple_parameter_specialize (fun _ : Fin p => .vf) (fun _ : Fin a => .rv)
    (fun j => (z j).val) (F.schema 0).domain_definable
  have h := gamma_rv_set_from_tuple_formula hD
  convert h using 1
  apply Set.ext
  intro x
  exact (Set.ext_iff.mp (F.schema_row_domain 0 z) x.2).symm

theorem GammaRVFamilyFormula.row_volume_definable (F : GammaRVFamilyFormula B p a k)
    (z : Fin p → VF (M := M)) :
    GammaGraphDefinable ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩
      (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 k) => F.rowVolume z x.2 y.2) := by
  have hz (j : Fin p) : sortEval SortTag.vf (z j).val := by
    simpa only [sortEval,iVF] using (z j).property
  have h := gamma_rv_tuple_relation_specialize (fun _ : Fin p => .vf) (fun j => (z j).val) hz
    (F.schema 0).volume_definable
  apply GammaGraphDefinable.congr h
  intro x y
  exact F.schema_row_volume 0 z x.2 y.2

theorem GammaRVFamilyFormula.realizeRow (F : GammaRVFamilyFormula B p a k)
    (z : Fin p → VF (M := M))
    (hfun : ∀ x : F.rowDomain z, ∃! y : Fin k → RV (M := M), F.rowVolume z x.val y)
    (hfinite : ∀ y : Fin k → RV (M := M), {x : F.rowDomain z | F.rowVolume z x.val y}.Finite) :
    Nonempty (GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) :=
  exists_gammaFiniteGraphPresentation (F.row_domain_definable z) (F.row_volume_definable z) hfun hfinite

theorem GammaRVFamilyFormula.exists_valid_schema {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (F : GammaRVFamilyFormula B p a k) (z : Fin p → VF (M := M))
    (hsupport : ∀ x y, F.rowVolume z x y → x ∈ F.rowDomain z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) :
    ∃ N : ℕ, (F.schema N).valid (fun j => (z j).val) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩
  have hsmall : Cardinal.mk C.real < κ := small_union_range hκ B.real hreal (fun j => (z j).val)
  obtain ⟨N,hN⟩ := @gammaRawObjectVolume_uniform_bound M sM hM C k κ hκ hs hsmall hgamma P.toGamma
  have hD := F.raw_row_domain_presented N z P
  have hV := F.raw_row_volume_presented N z hsupport P
  refine ⟨N,?_,?_,?_,?_⟩
  · intro j
    simpa only [sortEval,iVF] using (z j).property
  · intro x hx
    obtain ⟨y,hy,hu⟩ := gammaRawObjectVolume_unique P.toGamma.toGammaRVObject x ((hD x).mp hx)
    exact ⟨y,(hV x y).mpr hy,fun y' hy' => hu y' ((hV x y').mp hy')⟩
  · intro x y hxy
    obtain ⟨u,hu,_⟩ := (gammaRawObjectVolume_append_iff P.toGamma.toGammaRVObject x y).mp ((hV x y).mp hxy)
    exact (hD x).mpr ⟨u,hu⟩
  · intro y hy
    have he : {x | Fin.append (Fin.append (fun j => (z j).val) x) y ∈ (F.schema N).volume} =
        {x | Fin.append x y ∈ gammaRawObjectVolume P.toGamma.toGammaRVObject} := Set.ext (fun x => hV x y)
    change _ ∧ _
    rw [he]
    exact hN y hy

end IntegrationInACVF.Section6
