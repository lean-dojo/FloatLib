#!/usr/bin/env bash

set -euo pipefail

campaign=/efs/robert/floatlean-results/332491fd0acb7702b5730aa96bf5927063583d92/20260910T150728Z/ecosystem
result_dir="$campaign/results/daisy-rerun1"
work_dir=/work/daisy-rerun1

mkdir -p "$result_dir" "$work_dir"
exec > >(tee "$result_dir/run.log") 2>&1

started=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf 'suite=daisy\nattempt=2\nstarted=%s\nnode=%s\n' \
  "$started" "${NODE_NAME:-unknown}" > "$result_dir/metadata.env"

finish() {
  status=$?
  finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  printf 'status=%s\nfinished=%s\n' "$status" "$finished" \
    | tee "$result_dir/status.env"
  exit "$status"
}
trap finish EXIT

export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y --no-install-recommends \
  bash build-essential ca-certificates curl gcc g++ git libicu-dev \
  libmpfr6 libmpfr-dev locales make python3 time z3

mkdir -p /opt/java
curl -fsSL \
  'https://api.adoptium.net/v3/binary/latest/25/ga/linux/x64/jdk/hotspot/normal/eclipse' \
  -o /tmp/jdk25.tar.gz
tar -xzf /tmp/jdk25.tar.gz -C /opt/java --strip-components=1
export JAVA_HOME=/opt/java
export PATH="$JAVA_HOME/bin:$PATH"
java -version

curl -fsSL \
  'https://github.com/sbt/sbt/releases/download/v1.9.9/sbt-1.9.9.tgz' \
  -o /tmp/sbt.tgz
mkdir -p /opt/sbt
tar -xzf /tmp/sbt.tgz -C /opt/sbt --strip-components=1
export PATH="/opt/sbt/bin:$PATH"
sbt --script-version

git clone --no-tags https://github.com/malyzajko/daisy.git "$work_dir/src"
git -C "$work_dir/src" checkout --detach \
  6a6f47abdd231d3009444e9e1b8ce9febc28c27e
git -C "$work_dir/src" rev-parse HEAD

cd "$work_dir/src"
export LC_NUMERIC=C.UTF-8
export SBT_OPTS='-Xms1G -Xmx16G -Xss8M'
export JAVA_TOOL_OPTIONS='-Xss8M'

sbt -v -batch compile Test/compile
sbt -v -batch test
sbt -v -batch script
./regression/scripts/run_all.sh
