#!/usr/bin/env bash
set -euo pipefail

# These SDKs belong to the disposable GitHub Linux runner. None is used by
# the Lean/C++/Python verification jobs. Refuse accidental local execution.
if [[ "${GITHUB_ACTIONS:-}" != "true" || "${RUNNER_OS:-}" != "Linux" ]]; then
  echo "error: swap preparation is restricted to GitHub Actions Linux runners" >&2
  exit 1
fi
: "${RUNNER_TEMP:?RUNNER_TEMP is required}"

swap_path="$RUNNER_TEMP/recaman-kernel.swap"
required_kib=$((36 * 1024 * 1024))

available_kib() {
  df --output=avail "$RUNNER_TEMP" | awk 'NR == 2 {print $1}'
}

available="$(available_kib)"
if [[ ! "$available" =~ ^[0-9]+$ ]]; then
  echo "error: cannot determine available runner disk space" >&2
  exit 1
fi

if [[ "$available" -lt "$required_kib" ]]; then
  echo "Reclaiming unused runner SDKs before reserving kernel swap"
  sudo rm -rf -- \
    /usr/local/lib/android \
    /usr/share/dotnet \
    /opt/ghc \
    /opt/hostedtoolcache/CodeQL
  available="$(available_kib)"
fi

if [[ ! "$available" =~ ^[0-9]+$ ]] || [[ "$available" -lt "$required_kib" ]]; then
  echo "error: need 36 GiB free for 32 GiB swap and 4 GiB build space; available KiB: $available" >&2
  df -h "$RUNNER_TEMP"
  exit 1
fi

sudo fallocate -l 32G "$swap_path"
sudo chmod 600 "$swap_path"
sudo mkswap "$swap_path"
sudo swapon "$swap_path"
free -h
df -h "$RUNNER_TEMP"
