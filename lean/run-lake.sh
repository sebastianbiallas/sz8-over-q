#!/bin/sh
# Run lake in this directory. A compiler unpacked here (lean-4.34.0-rc2-darwin_aarch64/, from
# lean-toolchain.tar.zst) takes precedence over one on PATH (for example from elan).
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ -d "$project_dir/lean-4.34.0-rc2-darwin_aarch64/bin" ]; then
  PATH="$project_dir/lean-4.34.0-rc2-darwin_aarch64/bin:$PATH"
fi
XDG_CACHE_HOME="$project_dir/.lake/cache"
export PATH XDG_CACHE_HOME
cd "$project_dir"
exec lake "$@"
