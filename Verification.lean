import ChenRanks
import checks.ActualChenRanksAFRSVersionOneAudit
import checks.ActualCentralChenRanksAFRSVersionOneAudit

/-!
# Verification of the public interface

The imported audits check the full AFRS proposition, the complement's
fundamental-group quotients and the intrinsic component sums. These
additional queries display the public theorem types and their
transitive foundational dependencies.
-/

set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs false

#check @ChenRanks.AffineArrangement.chenRanks_affine
#check @ChenRanks.AffineArrangement.chenRanks_central
#print axioms ChenRanks.AffineArrangement.chenRanks_affine
#print axioms ChenRanks.AffineArrangement.chenRanks_central
