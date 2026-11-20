#!/usr/bin/env bash
# Regression test for scripts/lane-merge-guard's revert check (SW-4309).
#
# Creates throwaway branches from HEAD, with a --no-ff merge that adds one
# file and modifies another, then checks four lanes against that merge-base:
# a deletion of the added file passes with a note, restoring the modified file
# is refused, a lane that does both is refused, and a clean lane passes.
# Removes the branches and returns to the original branch on exit.
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"
original=$(git symbolic-ref --quiet --short HEAD) \
  || { echo 'lane-merge-guard.test: HEAD is detached' >&2; exit 2; }
[ -z "$(git status --porcelain)" ] \
  || { echo 'lane-merge-guard.test: the checkout has uncommitted changes' >&2; exit 2; }

id=$$
base="test/sw4309-guard-$id-base"
merge="test/sw4309-guard-$id-merge"
delete_lane="test/sw4309-guard-$id-delete"
restore_lane="test/sw4309-guard-$id-restore"
both_lane="test/sw4309-guard-$id-both"
clean_lane="test/sw4309-guard-$id-clean"
lanes=("$delete_lane" "$restore_lane" "$both_lane" "$clean_lane")
fixtures="sw4309-guard-test-$id"

cleanup() {
  local branch
  git switch --quiet "$original" 2>/dev/null || true
  for branch in "${lanes[@]}" "$merge" "$base"; do
    git branch -D "$branch" >/dev/null 2>&1 || true
  done
  rm -rf "$fixtures"
}
trap cleanup EXIT

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

# A base with a pre-merge version of a file, then merge M adds one file and
# changes that file, so M^1 has the old version and no added file.
git switch --quiet -c "$base"
mkdir -p "$fixtures"
printf 'pre-merge\n' > "$fixtures/modified.txt"
git add -- "$fixtures/modified.txt"
git commit --quiet --no-verify -m 'lane-merge-guard.test: base' -- "$fixtures/modified.txt"

git switch --quiet -c "$merge"
printf 'added by merge M\n' > "$fixtures/added.txt"
printf 'post-merge\n' > "$fixtures/modified.txt"
git add -- "$fixtures/added.txt" "$fixtures/modified.txt"
git commit --quiet --no-verify -m 'lane-merge-guard.test: merge M' \
  -- "$fixtures/added.txt" "$fixtures/modified.txt"

git switch --quiet "$base"
git merge --quiet --no-ff --no-commit "$merge"
git commit --quiet --no-verify -m 'lane-merge-guard.test: merge M into base'

# The four lanes all start after M.
git switch --quiet -c "$delete_lane" "$base"
git rm --quiet "$fixtures/added.txt"
git commit --quiet --no-verify -m 'lane-merge-guard.test: delete' \
  -- "$fixtures/added.txt"

git switch --quiet -c "$restore_lane" "$base"
printf 'pre-merge\n' > "$fixtures/modified.txt"
git add -- "$fixtures/modified.txt"
git commit --quiet --no-verify -m 'lane-merge-guard.test: restore' \
  -- "$fixtures/modified.txt"

git switch --quiet -c "$both_lane" "$base"
git rm --quiet "$fixtures/added.txt"
printf 'pre-merge\n' > "$fixtures/modified.txt"
git add -- "$fixtures/modified.txt"
git commit --quiet --no-verify -m 'lane-merge-guard.test: both' \
  -- "$fixtures/added.txt" "$fixtures/modified.txt"

git switch --quiet -c "$clean_lane" "$base"
printf 'clean lane change\n' > "$fixtures/clean.txt"
git add -- "$fixtures/clean.txt"
git commit --quiet --no-verify -m 'lane-merge-guard.test: clean' \
  -- "$fixtures/clean.txt"

guard=$root/scripts/lane-merge-guard
note="note: lane $delete_lane deletes files a recent merge added:"

run_guard() {
  set +e
  output=$("$guard" "$1" "$base" 2>&1)
  rc=$?
  set -e
}

run_guard "$delete_lane"
printf '%s\n' "$output"
[ "$rc" -eq 0 ] || fail "deletion lane exited $rc"
case "$output" in
  *"$note"*"$fixtures/added.txt"*) ;;
  *) fail 'deletion lane did not print the expected note' ;;
esac
echo 'ok 1: a lane deletion of a file a recent merge added passes with a note'

run_guard "$restore_lane"
printf '%s\n' "$output"
[ "$rc" -eq 1 ] || fail "restore lane exited $rc, expected 1"
case "$output" in
  *'refusing:'*"$fixtures/modified.txt"*) ;;
  *) fail 'restore lane was not refused for the modified file' ;;
esac
case "$output" in
  *'note:'*) fail 'restore lane printed a deletion note' ;;
esac
echo 'ok 2: restoring a modified file to its pre-merge version is refused'

run_guard "$both_lane"
printf '%s\n' "$output"
[ "$rc" -eq 1 ] || fail "both lane exited $rc, expected 1"
case "$output" in
  *'note: lane '*"$fixtures/added.txt"*) ;;
  *) fail 'both lane did not note the deletion' ;;
esac
case "$output" in
  *'refusing:'*"$fixtures/modified.txt"*) ;;
  *) fail 'both lane was not refused for the restored file' ;;
esac
echo 'ok 3: a lane that deletes one file and restores another is refused'

run_guard "$clean_lane"
printf '%s\n' "$output"
[ "$rc" -eq 0 ] || fail "clean lane exited $rc"
case "$output" in
  *'note:'*|*'refusing:'*) fail 'clean lane was flagged' ;;
esac
echo 'ok 4: a clean lane passes'

echo 'lane-merge-guard.test: all 4 passed'
