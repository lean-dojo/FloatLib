#!/usr/bin/env bash

set -euo pipefail

export RESULT_NAME=exblas-rerun6
export WORK_NAME=exblas-rerun6
export ATTEMPT=7

exec /bin/bash \
  /efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem/control/run-exblas-rerun3.sh
