import TwinPrimeExternal.GeneratedCertificate

/-!
# Final External-Certificate Endpoint

The theorem `arbitrarily_large_twins` is unconditional inside Lean after
importing the generated external certificate file.  Its sole non-Lean
dependency is the generated C++ certificate declaration named
`GeneratedCertificate.external_no_cofinalExceptionTail`.
-/

namespace TwinPrimeExternal

theorem no_cofinalExceptionTail :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) :=
  GeneratedCertificate.external_no_cofinalExceptionTail

theorem not_boundedTwinMids : Not BoundedTwinMids :=
  no_boundedTwinMids_of_no_cofinalExceptionTail no_cofinalExceptionTail

theorem arbitrarily_large_twins : ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    no_cofinalExceptionTail

end TwinPrimeExternal
