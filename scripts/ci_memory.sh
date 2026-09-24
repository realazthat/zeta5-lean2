#!/usr/bin/env bash
# The solution export needs more memory than a small hosted runner provides.
# Provision swap only on the disposable GitHub Actions machine.
set -euo pipefail
if [[ "${GITHUB_ACTIONS:-}" != true || "${RUNNER_ENVIRONMENT:-}" != github-hosted ]]; then
  echo "Memory provisioning is restricted to disposable GitHub-hosted runners" >&2
  exit 1
fi
: "${RUNNER_TEMP:?This script requires a GitHub Actions runner}"
free -h
df -h "$RUNNER_TEMP"
required_kib=$((16 * 1024 * 1024))
physical_kib=$(awk '/^MemTotal:/ {print $2}' /proc/meminfo)
swap_kib=$(awk '/^SwapTotal:/ {print $2}' /proc/meminfo)
missing_kib=$((required_kib - physical_kib - swap_kib))
if ((missing_kib > 0)); then
  extra_gib=$(((missing_kib + 1048575) / 1048576))
  available_bytes=$(df -B1 --output=avail "$RUNNER_TEMP" | tail -n 1)
  needed_bytes=$(((extra_gib + 12) * 1024 * 1024 * 1024))
  if ((available_bytes < needed_bytes)) && [[ -d /usr/local/lib/android/sdk ]]; then
    # This fixed SDK path is part of the pinned runner image, unused by Lean.
    [[ "$(realpath /usr/local/lib/android/sdk)" == /usr/local/lib/android/sdk ]]
    sudo rm -rf -- /usr/local/lib/android/sdk
    available_bytes=$(df -B1 --output=avail "$RUNNER_TEMP" | tail -n 1)
    df -h "$RUNNER_TEMP"
  fi
  if ((available_bytes < needed_bytes)); then
    echo "Insufficient disk for ${extra_gib} GiB swap plus 12 GiB build space" >&2
    exit 1
  fi
  swap_path="$RUNNER_TEMP/palomar-verification.swap"
  if [[ -e "$swap_path" ]]; then
    echo "Refusing to overwrite existing swap path: $swap_path" >&2
    exit 1
  fi
  sudo fallocate -l "${extra_gib}G" "$swap_path"
  sudo chmod 600 "$swap_path"
  sudo mkswap "$swap_path"
  sudo swapon "$swap_path"
fi
free -h
