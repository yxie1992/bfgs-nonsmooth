import BfgsVerification.Definitions
import BfgsVerification.CompressionAlgebra
import BfgsVerification.ScalarHierarchy
import BfgsVerification.ReciprocalGrowth
import BfgsVerification.PrincipalMinors
import BfgsVerification.CompressionDeterminant
import BfgsVerification.GramSchur
import BfgsVerification.BFGSUpdate
import BfgsVerification.BFGSCompression
import BfgsVerification.OrthogonalCoordinates
import BfgsVerification.QuantitativeGrowth
import BfgsVerification.Normalization
import BfgsVerification.EndToEnd
import BfgsVerification.ObjectiveEndToEnd

/-!
Module M's actual matrix hierarchy, objective bridge and reciprocal-growth chain. Consult
audit/STATUS.json for current build status and audited theorem statements.
-/
