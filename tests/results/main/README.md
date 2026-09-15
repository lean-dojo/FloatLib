# External test results

We keep the results of our external comparisons here, together with the logs,
source information, and scripts behind the reported numbers.

- `release/external/` holds the direct conformance and oracle campaign.
- `ecosystem/` holds broader upstream projects and numerical-testing tools.
- `provenance/` holds the immutable source archive, dirty
  worktree patch, and hash ledgers used by the release campaign.

Every level has a SHA-256 manifest. Run `tests/oracles/verify-main-result.sh`
from the repository root to check the files, campaign provenance, status
contracts, and regenerated plots.

The reports and figures use the current FloatLib name. Original source captures and
raw output retain the names recorded by the campaigns; their contents and source
hashes are unchanged. Result manifests cover the updated report labels and filenames.

The original Git history bundles contain unpublished manuscript history and are kept
private. Their recorded hashes remain in the original metadata. The public check verifies
the complete measured-source archive and every file against its source ledger; it does
not verify the original Git history. Maintainers can also check an original bundle with
`verify_campaign_provenance.py --repository-bundle PATH`.
