#!/usr/bin/env bash

set -euo pipefail

export RESULT_NAME=direct-oracles-rerun2
export WORK_NAME=floatlean-direct-oracles-rerun2
export ATTEMPT=2

exec /bin/bash \
  /efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem/control/run-direct-oracles.sh
