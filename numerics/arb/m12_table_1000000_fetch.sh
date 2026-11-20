#!/usr/bin/env bash
# Fetch and authenticate the inputs of one stage of the 1000000-bit Table 1 run.
# Usage: m12_table_1000000_fetch.sh SCOPE   (SCOPE = work or combine)
# The Lanczos endpoints are those of run 44313014167 (as in the 100000-bit run);
# every other input is an artifact named in m12_table_1000000_stage.json by run,
# artifact id, name and SHA-256 digest, from a successful run.
set -euo pipefail
scope="$1"
stage=m12_table_1000000_stage.json
mkdir -p sources inputs
run=44313014167
head=8fc451ce053a769087fb25ed16289018890bc926
gh api "repos/$GITHUB_REPOSITORY/actions/runs/$run" | jq -e --arg sha "$head" '.head_sha == $sha and .conclusion == "success"' > /dev/null
for spec in \
  '100 14431877216 8f2e19d47c0d0ff4011f23a915b6f3ba7c700616805f4ce5849c929dad66e784' \
  '200 14435228234 eb184d12ad6db434bbc533b0cfde30d83fa08f54b6917e54284ea4aeca8f2a26' \
  '400 14449268572 2155c46f7bef8ec70bb4bc6e5966b2ee2a485ab306299817640961fbc75ba2e6'; do
  read -r m id digest <<< "$spec"
  ep="repos/$GITHUB_REPOSITORY/actions/artifacts/$id"
  gh api "$ep" | jq -e --arg sha "$head" --arg digest "sha256:$digest" --arg name "m12-lanczos-$m" \
    '.workflow_run.head_sha == $sha and .workflow_run.id == 44313014167 and .digest == $digest and .name == $name and .expired == false' > /dev/null
  gh api "$ep/zip" > "sources/$m.zip"
  printf '%s  %s\n' "$digest" "sources/$m.zip" | sha256sum -c -
  unzip -o -j "sources/$m.zip" "m12-lanczos-$m.json" -d sources
done
jq -c --arg scope "$scope" '.inputs[] | select($scope == "combine" or .scope == "all")' "$stage" | while read -r item; do
  run=$(jq -r .run <<< "$item"); id=$(jq -r .id <<< "$item")
  name=$(jq -r .name <<< "$item"); digest=$(jq -r .digest <<< "$item")
  req=$(jq -r 'if has("require_success") then .require_success else true end' <<< "$item")
  gh api "repos/$GITHUB_REPOSITORY/actions/runs/$run" | jq -e --argjson req "$req" 'if $req then .conclusion == "success" else true end' > /dev/null
  ep="repos/$GITHUB_REPOSITORY/actions/artifacts/$id"
  gh api "$ep" | jq -e --argjson run "$run" --arg digest "sha256:$digest" --arg name "$name" \
    '.workflow_run.id == $run and .digest == $digest and .name == $name and .expired == false' > /dev/null
  gh api "$ep/zip" > "inputs/$id.zip"
  printf '%s  %s\n' "$digest" "inputs/$id.zip" | sha256sum -c -
  unzip -o -j -q "inputs/$id.zip" '*.json' -d inputs
  rm "inputs/$id.zip"
  echo "INPUT $name run $run artifact $id sha256:$digest"
done
