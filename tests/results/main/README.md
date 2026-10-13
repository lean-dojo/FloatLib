# External test results

We keep the results of our external comparisons here, together with the logs,
source information, and scripts behind the reported numbers.

- `release/external/` holds the direct conformance and oracle campaign.
- `ecosystem/` holds broader upstream projects and numerical-testing tools.
- `provenance/` holds the environment and source information recorded by the release campaign.

Every level has a SHA-256 manifest. Run `tests/oracles/verify-main-result.sh`
from the repository root to check the files, numerical results, status
contracts, and regenerated plots.

The reports and figures use the current FloatLib name. Raw output retains the names recorded by
its campaign. Private mount paths, hostnames, and registry addresses use publication placeholders.
Numerical results are unchanged. These saved measurements describe their recorded environment;
the checks reproduce their tables and plots, rather than rerunning the campaigns.
