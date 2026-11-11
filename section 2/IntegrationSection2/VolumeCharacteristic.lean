import Section3.Average

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section2.VolumeCharacteristic

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem charZero (h00 : M ⊨ Axioms.ACVF00) : CharZero (VFType (M := M)) := by
  apply charZero_of_inj_zero
  intro n hn
  by_contra hn0
  have hunit := Average.nat_unit h00 n hn0
  have hz : Average.val (n : VFType (M := M)) = iRVZero := by
    rw [hn]
    exact Average.val_zero
  exact RVCalc.rv_one_ne_zero hM
    (RVCalc.le_infty_eq hM (rv_one_mem hM) (hz ▸ hunit))

end IntegrationInACVF.Section2.VolumeCharacteristic
