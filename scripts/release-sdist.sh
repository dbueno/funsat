#!/usr/bin/env sh

set -eu

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
output_dir=${1:-"$repo_root/sdist"}

mkdir -p "$output_dir"

printf 'Building source distributions into %s\n' "$output_dir"
(cd "$repo_root" && cabal sdist all --output-directory="$output_dir")

printf '\nGenerated tarballs:\n'
find "$output_dir" -maxdepth 1 -type f -name '*.tar.gz' | sort

printf '\nUpload order:\n'
printf '1. bitset\n'
printf '2. parse-dimacs\n'
printf '3. funsat\n'
