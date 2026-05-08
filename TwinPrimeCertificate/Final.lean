import TwinPrimeCertificate.TailInductionCertificate

/-!
# Final Tail-Induction Endpoint

This file exposes the final endpoint in the dependency order we want:

* a checked tail-induction certificate proves that no cofinal exceptional tail
  exists;
* no cofinal exceptional tail proves unbounded twin-prime midpoints;
* unbounded twin-prime midpoints prove arbitrarily large twin primes.
-/

namespace TwinPrimeCertificate

theorem no_cofinalExceptionTail
    (cert : MidpointTailInductionCertificate) :
    Not (exists B, CofinalExceptionTail MidpointExceptionalPrime B) :=
  no_cofinalExceptionTail_of_tailInductionCertificate cert

theorem not_boundedTwinMids
    (cert : MidpointTailInductionCertificate) :
    Not BoundedTwinMids :=
  no_boundedTwinMids_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail cert)

theorem arbitrarily_large_twins
    (cert : MidpointTailInductionCertificate) :
    ArbitrarilyLargeTwins :=
  arbitrarily_large_twins_of_no_cofinalExceptionTail
    (no_cofinalExceptionTail cert)

end TwinPrimeCertificate

