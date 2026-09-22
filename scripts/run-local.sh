#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
build_root="${QUADRATURE_BUILD_ROOT:-/mnt/build/robert/leanquadrature/LeanQuadrature}"
build_root="$(realpath -m "$build_root")"
case "$build_root" in
  /efs|/efs/*) printf 'Build directory must be on local storage.\n' >&2; exit 1 ;;
esac
mkdir -p "$build_root"
exec {lock_fd}>"$build_root/.build-lock"
flock "$lock_fd"
rsync -a --delete --exclude='.git/' --exclude='.lake/' --exclude='.build-lock' \
  "$repo_root/" "$build_root/"
cd "$build_root"
exec "$@"
