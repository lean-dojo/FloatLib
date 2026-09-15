# FloatLean external ecosystem campaign

This directory records a clean, pinned run against third-party floating-point
test suites and tools.  Upstream self-tests and FloatLean interoperability tests
are reported separately: a project passing its own tests is not evidence that it
agrees with FloatLean.

- FloatLean revision: `332491fd0acb7702b5730aa96bf5927063583d92`
- Campaign start: `2026-09-10T15:07:28Z`
- Cluster limit: at most ten CPU jobs at once
- Initial campaign image: Ubuntu 24.04
- Initial campaign request: 180 vCPU and 300 GiB per job
- FLiT retry image: pinned Ubuntu 22.04 image
- FLiT retry request: one sequential 96 vCPU, 160 GiB job

The first wave exercises the upstream suites.  Later waves use FloatLean adapters
for IBM FPgen vectors, SoftPosit, FPCore, correctly-rounded libm vectors, exact
reductions, and generated SMT-LIB floating-point problems.

The fifth FLiT runner corrects a retention check in the fourth attempt. FLiT's
generated Makefile uses `*-out` as a GNU Make intermediate and produces
`*-out-comparison.csv` as the final target. The fourth runner incorrectly
required both. The selected run follows FLiT's documented workflow: retain all
140 comparison CSVs for each variant, import them into SQLite, and verify the
database. The failed fourth attempt remains in the launch history instead of
being rewritten.
