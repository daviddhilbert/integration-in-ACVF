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

/-!
# Integration in algebraically closed valued fields

The predecessor supplies the common ACVF-QE language and the Section 3/4
libraries used here. Its later sections are checked separately by CI.
The sequel's Section 3 library develops Definition 3.1 and the finite-exception
geometry used in Lemma 3.2. Its status distinguishes these checked components
from the remaining connections to the ACVF imaginary expansion.
-/

/- Section 6 exports the RV[k] and graded RV[*] formalization, including
   integration, definable families, Fubini and localization. The authorized
   unfinished Section 5.8 input remains explicit in the final theorem types. -/
