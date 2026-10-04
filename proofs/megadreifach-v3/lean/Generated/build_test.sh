#!/bin/bash
set -euo pipefail
if ! command -v lake >/dev/null 2>&1; then
  echo "lean-build: lake not on PATH" >&2
  exit 127
fi
prefix=""
if command -v lean >/dev/null 2>&1; then
  prefix="$(lean --print-prefix 2>/dev/null || true)"
fi
if [ -n "$prefix" ]; then
  export LEAN_SYSROOT="$prefix"
  export LEAN_PATH="${LEAN_PATH:-$prefix/lib/lean}"
fi
echo "lean-build: lean=$(command -v lean || echo missing) prefix=${prefix:-unset} lake=$(command -v lake)" >&2
lake build
bin="./.lake/build/bin/megadreifach_test"
if [ ! -f "$bin" ]; then
  echo "lean-build: missing $bin after lake build" >&2
  ls -la .lake/build/bin >&2 || ls -laR .lake >&2 || true
  exit 127
fi
chmod +x "$bin"
bindir="$(cd "$(dirname "$bin")" && pwd)"
if [ -n "$prefix" ]; then
  case "$(uname -s)" in
    Darwin)
      # Bake absolute + @loader_path rpaths so dyld does not need
      # DYLD_* (stripped by SIP when the parent is /bin/bash).
      install_name_tool -add_rpath "$prefix/lib/lean" "$bin" 2>/dev/null || true
      install_name_tool -add_rpath "$prefix/lib" "$bin" 2>/dev/null || true
      install_name_tool -add_rpath "@loader_path" "$bin" 2>/dev/null || true
      # Sandbox-proof fallback: copy @rpath dylibs next to the exe.
      if command -v otool >/dev/null 2>&1; then
        otool -L "$bin" | awk '/@rpath\//{print $1}' | while read -r ref; do
          name="${ref##*/}"
          if [ -z "$name" ]; then continue; fi
          if [ -f "$bindir/$name" ]; then continue; fi
          for dir in "$prefix/lib/lean" "$prefix/lib"; do
            if [ -f "$dir/$name" ]; then
              cp "$dir/$name" "$bindir/$name"
              break
            fi
          done
        done
        echo "lean-build: otool -L $bin" >&2
        otool -L "$bin" >&2 || true
        echo "lean-build: LC_RPATH" >&2
        otool -l "$bin" | awk '/LC_RPATH/,/path/{print}' >&2 || true
      fi
      # install_name_tool invalidates the ad-hoc signature; resign.
      if command -v codesign >/dev/null 2>&1; then
        codesign --force --sign - "$bin" >&2 || true
      fi
      ;;
  esac
fi
