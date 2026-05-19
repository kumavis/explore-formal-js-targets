#!/usr/bin/env bash
# Build a Coq problem end-to-end:
#   <ModuleStem>.v   →  coqc      →  <module>.ml + .mli
#                       sed       →  fix OCaml 5 Pervasives→Stdlib rename
#                       ocamlc    →  *.cmo + *.cmi
#                       ocamlc    →  *.byte
#                       js_of_ocaml → <module>.js
#
# Usage: coq-build.sh <ModuleStem>
#   Looks for ./<ModuleStem>.v and ./driver.ml in the current directory.
#   Emits ./<module-lowercase>.js.
set -euo pipefail
stem_uc="$1"
stem_lc=$(printf %s "$stem_uc" | tr '[:upper:]' '[:lower:]')

rm -f ./*.vo ./*.glob "${stem_lc}.ml" "${stem_lc}.mli" ./*.cmo ./*.cmi \
      "${stem_lc}.byte" "${stem_lc}.js"

coqc "${stem_uc}.v"
sed -i 's/Pervasives/Stdlib/g' "${stem_lc}.ml" "${stem_lc}.mli"

ocamlc -c "${stem_lc}.mli"
ocamlc -c "${stem_lc}.ml"
ocamlc -c driver.ml
ocamlc -o "${stem_lc}.byte" "${stem_lc}.cmo" driver.cmo
js_of_ocaml "${stem_lc}.byte" -o "${stem_lc}.js"
