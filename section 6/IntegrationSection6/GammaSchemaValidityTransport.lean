import IntegrationSection6.GammaMapRowTransport
import IntegrationSection6.GammaAdmissibilitySchemata
import IntegrationSection6.GammaIsomorphismSchemata

/-! Validity of actual finite object, admissibility and weighted chart
schemata depends on their literal rows and fixed numerical metadata.
It therefore transports from VF parameters to proper RV key tuples. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a b k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem GammaFiniteRVSchema.valid_of_rowAgreement
    (F : GammaFiniteRVSchema B p a k sp) (G : GammaFiniteRVSchema B q a k sq)
    (z : Fin p → M) (t : Fin q → M) (ht : ∀ j, sortEval (sq j) (t j))
    (hBound : F.bound = G.bound) (hRows : GammaSchemaRowAgreement F z G t) (hF : F.valid z) : G.valid t := by
  change finiteMapRowValid sq (fun _ => .rv) G.domain G.volume G.bound t
  rw [← hBound]
  exact finiteMapRowValid_of_rows ht hRows.1 hRows.2 hF

theorem weightedChartRowValid_of_rows
    {H : Set (Fin ((p+a)+b) → M)} {H' : Set (Fin ((q+a)+b) → M)}
    {V : Set (Fin ((p+a)+k) → M)} {V' : Set (Fin ((q+a)+k) → M)}
    {W : Set (Fin ((p+b)+k) → M)} {W' : Set (Fin ((q+b)+k) → M)}
    {z : Fin p → M} {t : Fin q → M}
    (ht : ∀ j, sortEval (sq j) (t j))
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔ Fin.append (Fin.append t x) y ∈ H')
    (hV : ∀ x y, Fin.append (Fin.append z x) y ∈ V ↔ Fin.append (Fin.append t x) y ∈ V')
    (hW : ∀ x y, Fin.append (Fin.append z x) y ∈ W ↔ Fin.append (Fin.append t x) y ∈ W')
    (h : weightedChartRowValid sp H V W z) : weightedChartRowValid sq H' V' W' t := by
  refine ⟨ht,?_⟩
  intro r hr hh hv hw
  exact h.2 r hr ((hH _ _).mpr hh) ((hV _ _).mpr hv) ((hW _ _).mpr hw)

theorem GammaFiniteRVIsoSchema.valid_of_rowAgreement
    (F : GammaFiniteRVIsoSchema B p a b k sp) (G : GammaFiniteRVIsoSchema B q a b k sq)
    (z : Fin p → M) (t : Fin q → M) (ht : ∀ j, sortEval (sq j) (t j))
    (hSourceBound : F.source.bound = G.source.bound) (hTargetBound : F.target.bound = G.target.bound)
    (hSource : GammaSchemaRowAgreement F.source z G.source t)
    (hTarget : GammaSchemaRowAgreement F.target z G.target t)
    (hChart : ∀ x y, Fin.append (Fin.append z x) y ∈ F.chart ↔ Fin.append (Fin.append t x) y ∈ G.chart)
    (hF : F.valid z) : G.valid t :=
  ⟨F.source.valid_of_rowAgreement G.source z t ht hSourceBound hSource hF.1,
    F.target.valid_of_rowAgreement G.target z t ht hTargetBound hTarget hF.2.1,
    bijectiveMapRowValid_of_rows ht hSource.1 hTarget.1 hChart hF.2.2.1,
    weightedChartRowValid_of_rows ht hChart hSource.2 hTarget.2 hF.2.2.2⟩

theorem GammaFiniteAdmissibilitySchema.valid_of_rowAgreement
    (F : GammaFiniteAdmissibilitySchema B p a k sp) (G : GammaFiniteAdmissibilitySchema B q a k sq)
    (z : Fin p → M) (t : Fin q → M) (ht : ∀ j, sortEval (sq j) (t j))
    (hObjectBound : F.object.bound = G.object.bound) (hBound : F.bound = G.bound)
    (hCoordinate : F.coordinate = G.coordinate)
    (hRows : GammaSchemaRowAgreement F.object z G.object t) (hF : F.valid z) : G.valid t := by
  have hImage (r : Fin k → M) : Fin.append z r ∈ tupleVolumeImage F.object.volume ↔
      Fin.append t r ∈ tupleVolumeImage G.object.volume :=
    (tupleVolumeImage_append_iff F.object.volume z r).trans
      ((exists_congr (fun x => hRows.2 x r)).trans (tupleVolumeImage_append_iff G.object.volume t r).symm)
  refine ⟨F.object.valid_of_rowAgreement G.object z t ht hObjectBound hRows hF.1,?_,?_⟩
  · intro r hr
    have hn := hF.2.1 r ((hImage r).mpr hr)
    rwa [hCoordinate] at hn
  · intro u hu
    have he : {r | Fin.append t r ∈ tupleVolumeImage G.object.volume ∧ ∀ j, j ≠ G.coordinate → r j = u j} =
        {r | Fin.append z r ∈ tupleVolumeImage F.object.volume ∧ ∀ j, j ≠ F.coordinate → r j = u j} := by
      apply Set.ext
      intro r
      exact and_congr (hImage r).symm (by rw [hCoordinate])
    rw [he,← hBound]
    exact hF.2.2 u hu

end IntegrationInACVF.Section6
