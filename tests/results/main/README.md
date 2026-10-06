# External test results

We keep the results of our external comparisons here, together with the logs,
source information, and scripts behind the reported numbers.

- `release/external/` holds the direct conformance and oracle campaign.
- `ecosystem/` holds broader upstream projects and numerical-testing tools.
- `provenance/` holds the published source archive, dirty
  worktree patch, and hash ledgers used by the release campaign.

Every level has a SHA-256 manifest. Run `tests/oracles/verify-main-result.sh`
from the repository root to check the files, campaign provenance, status
contracts, and regenerated plots.

The reports and figures use the current FloatLib name. Source captures and raw output retain the names recorded by the campaigns. Private
mount paths, hostnames, and registry addresses have been replaced with publication
placeholders. Numerical results are unchanged. Original source hashes remain in the
ledgers; `provenance/public-source-archive.json` records the original and published
hashes of redacted archive members. Result manifests authenticate the published bytes.

The original Git history bundles contain unpublished manuscript history and are kept
private. Their recorded hashes remain in the original metadata. The public check verifies
each published source member against its source ledger or explicit redaction receipt; it does
not verify the original Git history. Maintainers can also check an original bundle with
`verify_campaign_provenance.py --repository-bundle PATH`.
