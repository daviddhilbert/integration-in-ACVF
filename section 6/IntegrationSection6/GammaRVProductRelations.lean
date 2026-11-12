import IntegrationSection6.GammaRVProductGraphs

/-! Cartesian products of full Gamma graphs use only real coordinate
projections and retain the original named base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b c d : ℕ}

theorem gamma_rv_relation_product
    {R : Point (M := M) 0 a → Point (M := M) 0 b → Prop}
    {T : Point (M := M) 0 c → Point (M := M) 0 d → Prop}
    (hR : GammaGraphDefinable B R) (hT : GammaGraphDefinable B T) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 (a+c)) (q : Point (M := M) 0 (b+d)) =>
      R (Fin.elim0,fun j => p.2 (Fin.castAdd c j)) (Fin.elim0,fun j => q.2 (Fin.castAdd d j)) ∧
      T (Fin.elim0,fun j => p.2 (Fin.natAdd a j)) (Fin.elim0,fun j => q.2 (Fin.natAdd b j))) :=
  (hR.preimage_maps (rvCoordinatePointMap (Fin.castAdd c) B.real)
    (rvCoordinatePointMap (Fin.castAdd d) B.real)).inter
  (hT.preimage_maps (rvCoordinatePointMap (Fin.natAdd a) B.real)
    (rvCoordinatePointMap (Fin.natAdd b) B.real))

end IntegrationInACVF.Section6
