# Sourced by launchers. Copies the bootstrap-recorded host files and the pinned
# overlay into a fresh private directory, then hashes the copies. Callers run
# only staged files, so a check cannot be separated from the bytes that load.
vor_overlay_sha256=480e26c610b593b66f87118ea2fbeacaf34201e42f2279a09decfb9481879168
case "$(uname -s):$(uname -m)" in
  Linux:x86_64|Linux:aarch64)
    vor_archive_sha256=c57f47586894534b9797daf5c0cc65c58dc6fb89d6ea6f0c2b48ac64de66d010 ;;
  Darwin:arm64)
    vor_archive_sha256=1dbbdfd4dbfc64383edf2ee08a788cb410bb3f5104e3b6b32204e443baeb3ff9 ;;
  *) vor_archive_sha256=unsupported ;;
esac
vor_host_path=".tools/host-path-$(uname -s)-$(uname -m)"
vor_identity=".tools/host-identity-$(uname -s)-$(uname -m)"

vor_hash() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d ' ' -f 1
  else shasum -a 256 "$1" | cut -d ' ' -f 1; fi
}

# Record every file the host loads (bin/ and lib/ under its root) against the
# verified archive. Only bootstrap calls this, immediately after a fresh install.
vor_record_identity() {
  root=$(dirname "$(dirname "$1")")
  {
    printf 'archive %s\n' "$vor_archive_sha256"
    (cd "$root" && find bin lib -type f | LC_ALL=C sort) | while read -r file; do
      printf '%s %s\n' "$(vor_hash "$root/$file")" "$file"
    done
  } > "$vor_identity.partial"
  grep -q ' bin/shen-scheme$' "$vor_identity.partial" || {
    echo 'Host identity is missing bin/shen-scheme.' >&2; exit 1;
  }
  mv "$vor_identity.partial" "$vor_identity"
}

vor_refuse() { echo "Host identity mismatch: $1 (run make bootstrap)." >&2; exit 1; }

# Sets vor_stage, vor_host and vor_overlay. Exits on any mismatch.
vor_stage_host() {
  [ -f "$vor_host_path" ] && [ -f "$vor_identity" ] && [ -f .tools/t-star-pr117.shen ] || {
    echo 'Run make bootstrap first.' >&2; exit 2;
  }
  vor_tools_root=$(cd .tools && pwd -P)
  root=$(cd "$(dirname "$(dirname "$(cat "$vor_host_path")")")" && pwd -P)
  case "$root/" in "$vor_tools_root/"*) ;; *) vor_refuse runtime-root ;; esac
  vor_stage=$(mktemp -d "${TMPDIR:-/tmp}/vor-host.XXXXXX")
  trap 'rm -rf "$vor_stage"' EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
  [ "$(head -n 1 "$vor_identity")" = "archive $vor_archive_sha256" ] || vor_refuse archive
  tail -n +2 "$vor_identity" > "$vor_stage/identity"
  while read -r digest file; do
    case "$file" in bin/*|lib/*) ;; *) vor_refuse "$file" ;; esac
    case "$file" in *..*) vor_refuse "$file" ;; esac
    [ ! -L "$root/$file" ] || vor_refuse "$file"
    vor_source_dir=$(cd "$root/$(dirname "$file")" && pwd -P)
    case "$vor_source_dir/" in "$vor_tools_root/"*) ;; *) vor_refuse "$file" ;; esac
    mkdir -p "$vor_stage/host/$(dirname "$file")"
    cp "$root/$file" "$vor_stage/host/$file"
    [ "$(vor_hash "$vor_stage/host/$file")" = "$digest" ] || vor_refuse "$file"
  done < "$vor_stage/identity"
  vor_host="$vor_stage/host/bin/shen-scheme"
  [ -f "$vor_host" ] || vor_refuse bin/shen-scheme
  chmod 0700 "$vor_host"
  vor_overlay="$vor_stage/t-star-pr117.shen"
  cp .tools/t-star-pr117.shen "$vor_overlay"
  [ "$(vor_hash "$vor_overlay")" = "$vor_overlay_sha256" ] || {
    echo 'PR 117 typechecker checksum mismatch' >&2; exit 1;
  }
}
