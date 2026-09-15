The pinned FPBench workflow target named `filter-test` calls
`test-evaluate.sh`, not `test-filter.sh`. The maintained workflow targets
passed. We also ran the standalone filter script so this archive does not hide
that discrepancy; its raw status and output are recorded in outcome.env and
filter-standalone.log.
