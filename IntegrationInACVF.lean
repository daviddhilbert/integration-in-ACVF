import IntegrationSection6.Library
import ACVFQE
import IntegrationSection3.Library
import IntegrationSection3.FieldLibrary
import IntegrationSection3.ProfileLibrary
import IntegrationSection3.CoordinateLibrary
import IntegrationSection2.Library
import IntegrationSection3ACVF.Library
import IntegrationSection4.Library
import IntegrationSection5.Library
import Integration7.Library

/-!
# Integration in algebraically closed valued fields

The predecessor supplies the common ACVF-QE language and the Section 3/4
libraries used here. Its later sections are checked separately by CI.
Sections 2–7 supply the checked integration development in the accepted scopes.
The blueprint records the numbered results, exact source links, standing
hypotheses and approved corrections. See blueprint/README.md and PROJECT-AUDIT.md.
-/

/- Section 6 exports the RV[k] and graded RV[*] formalization, including
   integration, definable families, Fubini and localization. The closed
   generated-base entrypoints in IntegrationInACVF.Section7.CompletedSection6
   derive the needed finite-VF-parameter inputs from the completed Section 5
   theorem. Their standing model, saturation and parameter hypotheses remain
   explicit. Integration7.HKCorrectedSection7Results exports the completed
   weighted measured-zero class algebra and raw/normalized function results. -/
