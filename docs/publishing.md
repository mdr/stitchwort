# Publishing the playground

The playground is a folder of static files (`nix build .#playground`). The
workflow `.github/workflows/playground.yml` builds it on GitHub Actions and
publishes it to GitHub Pages at `https://mdr.github.io/stitchwort/`. Written
for SW-173 (D533) on 22 October 2026. **Nothing has been pushed or enabled**:
the steps below are for you to run.

## Going live

1. Push the branch (or merge it) so `.github/workflows/playground.yml` is on
   the default branch. A `workflow_dispatch` workflow only appears in the
   Actions tab once its file is on the default branch.
2. Enable Pages with the workflow as its source. Either:
   - Settings, Pages, "Build and deployment", Source: **GitHub Actions**; or
   - the REST API (shown, not run; needs admin rights on the repository):

     ```sh
     gh api -X POST repos/mdr/stitchwort/pages -f build_type=workflow
     # if a site already exists, change its build type instead:
     gh api -X PUT repos/mdr/stitchwort/pages -f build_type=workflow
     ```
3. Run it: Actions tab, "Playground", Run workflow (branch `main`); or
   `gh workflow run playground.yml`. The first run builds the Rust
   dependencies for WebAssembly from scratch (a few minutes; later runs reuse
   the cache). The `deploy` job prints the site's URL.
4. Check the site: the page loads, "Check every day" works, and
   `https://mdr.github.io/stitchwort/pkg/version.json` answers.

To publish on every push to `main` that could change the site, uncomment the
`push:` block in the workflow's `on:` section (it has a `paths:` filter).

The first run is also the first time the Linux build runs: the Nix build was
checked on macOS only (`nix build .#playground` there; `x86_64-linux`
evaluates). A Linux-only failure would show in the `build` job.

## What is published

The whole `nix build .#playground` output: `index.html`,
`playground-worker.js` and `pkg/` (the WebAssembly, its bindings,
`version.json` and `pkg/projects/aoc/`). `pkg/projects/aoc/` includes the
**real puzzle inputs** (`inputs/YYYY/day*.txt`, D119). Once public, they are
public; the Advent of Code FAQ asks people not to publish them (see
`docs/proposals/playground-projects.md` §10.3, [A1]). Decide before the first
run whether that is acceptable.

## Caching

Browser side (built, §10.2 of the playground note): `pkg/version.json` holds
`{"compiler": H, "projects": H}`, short hashes of the compiler's files (the
WebAssembly, the bindings, the worker script) and of everything under
`pkg/projects/`. The page fetches it with `cache: "no-cache"` and then asks
for the compiler as `?v=<compiler>` and for the project files as
`?v=<projects>`. GitHub Pages sends `cache-control: max-age=600`, so without
the hash a returning visitor could get a ten-minute-old script next to a new
WebAssembly file; with it, a browser reuses the compiler until a build
changes it. `web/write-version.sh` writes the file; `web/build.sh` and the
`playground` package both call it.

CI side: `magic-nix-cache-action` keeps the Nix store in GitHub's Actions
cache (no account, no secrets). Its limits (below) matter little for a
manual, occasional workflow. **Upgrade paths**, in order of effort:

- Cachix (free for open source, 5 GB): create a cache, add a repository
  secret `CACHIX_AUTH_TOKEN`, replace the magic-nix-cache step with
  `cachix/cachix-action` (`name: <cache>`, `authToken`). This also gives a
  cache you can use locally.
- FlakeHub Cache: paid plans only; swap the installer step for the one in its
  docs (it needs `id-token: write` on the build job).
- `nix-community/cache-nix-action@v7`: also no secrets, caches the whole
  store in the Actions cache with explicit garbage collection, more to
  configure. Worth it only if magic-nix-cache's API use breaks.

## Research (22 October 2026)

What was checked, where, and what was seen. "Inferred" marks my own
conclusion, not a source's statement.

**Nix installer action.**
- `DeterminateSystems/determinate-nix-action`, latest `v3.23.3` (18 Oct
  2026), with a moving `v3` tag; its README supports pinning to an exact
  release and gives `permissions: id-token: write` only for FlakeHub.
  <https://github.com/DeterminateSystems/determinate-nix-action>
- `DeterminateSystems/nix-installer-action`, latest `v23` (9 Sep 2026); its
  README uses `@main` in every example, says it installs Determinate Nix by
  default, that its `flakehub` input is deprecated, and sends FlakeHub users
  to `determinate-nix-action`. <https://github.com/DeterminateSystems/nix-installer-action>
- `cachix/install-nix-action`, latest `v31.11.2` (14 Oct 2026), moving `v31`
  tag, installs upstream Nix; also what nix.dev's CI guide uses (the guide's
  example is an old version, `v25`).
  <https://github.com/cachix/install-nix-action>,
  <https://nix.dev/guides/recipes/continuous-integration-github-actions.html>
- Chosen: `determinate-nix-action` (the vendor's current action, versioned
  with the Nix it installs, the one the magic-nix-cache documentation pairs
  with). `cachix/install-nix-action@v31` is an equally valid choice if
  upstream Nix is preferred (inferred: both give flakes; the flake has no
  special needs).

**Binary cache, no secrets today.**
- `DeterminateSystems/magic-nix-cache-action`: "No secrets", free, stores in
  the GitHub Actions cache, works for forks and PRs, CI-only (not a public
  cache), subject to Actions cache rate limits (HTTP 429s are tolerated and
  do not fail CI); latest `v15` (9 Sep 2026).
  <https://github.com/DeterminateSystems/magic-nix-cache-action>
  History: it stopped working on 1 Feb 2025 when GitHub retired its old cache
  API, and came back on 13 June 2025 using the new, undocumented one; the
  post says this rests on reverse engineering and "could change at any time".
  <https://determinate.systems/blog/bringing-back-magic-nix-cache-action>
  A third-party report of `TwirpErrorResponse ResourceExhausted` failures
  from the 10 GB limit was found in search results, not verified.
- `nix-community/cache-nix-action`, latest `v7` (8 Jan 2026): no secrets
  (default `github.token`), 10 GB per repository, Nix 2.24+; needs an
  installer first and explicit GC settings.
  <https://github.com/nix-community/cache-nix-action>
- Cachix: free 5 GB for open-source projects; needs an account, a cache and
  a secret (`CACHIX_AUTH_TOKEN` or a signing key) to push.
  <https://www.cachix.org/pricing>,
  <https://nix.dev/guides/recipes/continuous-integration-github-actions.html>
- FlakeHub Cache: "available only on paid plans".
  <https://docs.determinate.systems/flakehub/cache>
- Chosen: magic-nix-cache with `use-gha-cache: true`, `use-flakehub: false`
  (the action's own inputs, from its `action.yml` at `v15`).
- Inferred: a cache saved by a run on `main` is readable by later runs on
  `main`; a run from another branch cannot read the cache of another
  branch's runs (GitHub's cache semantics, per the magic-nix-cache README's
  "same semantics as the GitHub Actions cache"). Run the workflow from `main`.

**Pages actions (latest release, date seen).**
- `actions/checkout` `v7.0.1` (20 Jul 2026). `v7.0.0` blocks checking out
  fork pull requests under `pull_request_target`/`workflow_run`; irrelevant
  here. <https://github.com/actions/checkout/releases>
- `actions/configure-pages` `v6.0.0` (25 Mar 2026): moved to Node 24.
  <https://github.com/actions/configure-pages/releases>
- `actions/upload-pages-artifact` `v5.0.0` (10 Apr 2026). `v4.0.0` (Aug
  2025) stopped including dotfiles by default (nothing here is a dotfile).
  <https://github.com/actions/upload-pages-artifact/releases>
- `actions/deploy-pages` `v5.0.1` (1 Sep 2026): v5 moved to Node 24; not for
  GitHub Enterprise Server. <https://github.com/actions/deploy-pages>
- GitHub's Pages documentation still shows older versions in its example
  (`configure-pages@v5`, `upload-pages-artifact@v4`, `deploy-pages@v4`):
  the docs lag the releases. The starter workflow `pages/static.yml`
  (fetched 22 Oct 2026) already uses `deploy-pages@v5` and gives the
  permissions (`contents: read`, `pages: write`, `id-token: write`),
  `concurrency: {group: pages, cancel-in-progress: false}` and the
  `github-pages` environment used here.
  <https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages>,
  <https://github.com/actions/starter-workflows/blob/main/pages/static.yml>

**Symlinks.** The artifact's tar must not contain symbolic or hard links
(upload-pages-artifact's README). But the action archives with
`tar --dereference --hard-dereference --directory "$INPUT_PATH"` (its
`action.yml`, read from `main`, 22 Oct 2026), so `path: result` (a symlink
into the Nix store) can be given as it is; no copy step. The artifact's
limits: 10 GB absolute, 1 GB supported (the playground is about 10 MB).

**Pinning.** GitHub's security guidance recommends pinning third-party
actions to a full commit SHA (a tag can be moved), with a lockfile
superseding that where available.
<https://docs.github.com/en/actions/reference/security/secure-use>
So: the two Determinate actions are pinned by SHA (with the release in a
comment); the `actions/*` actions use their major tag (GitHub's own; inferred
acceptable). Dependabot's `github-actions` ecosystem can update both.

**Runner.** `ubuntu-latest` is Ubuntu 24.04 (the `actions/runner-images`
README table; `ubuntu-26.04` also exists). A standard public-repository Linux
runner has 4 vCPU, 16 GB RAM and 14 GB SSD
(<https://docs.github.com/en/actions/reference/runners/github-hosted-runners>).
Inferred: 14 GB is enough for this build (the playground build here produced
a 4.6 MB WebAssembly file from a Rust release build); unmeasured on Linux.
If a build ever runs out of disk, free space first (remove the preinstalled
Android SDK) rather than paying for a larger runner.

**Enabling Pages from the CLI.** `POST /repos/{owner}/{repo}/pages` with
`build_type=workflow` (or `PUT` to change an existing site's), needing
repository admin rights.
<https://docs.github.com/en/rest/pages/pages>
The Pages "Source" documentation only describes the Settings route.
<https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site>

## Links to examples and days

The Example dropdown's entries have direct links (the fragment, so they work
under any path, such as `/stitchwort/`):

| Link | Opens |
|---|---|
| `#example/proofs-about-lists` | Proofs about lists |
| `#example/safe-division` | Safe division |
| `#example/tests` | Tests |
| `#example/abilities-and-handlers` | Abilities and handlers |
| `#example/input-and-output-main` | Input and output: main |
| `#example/extract-to-javascript` | Extract to JavaScript |
| `#aoc/YYYY/dayNN` (`#aoc/2025/day01`, `#aoc/2024/day01` and so on) | The AoC project at that day's program, as the dropdown's "Day N" under "Advent of Code YYYY" does |

An example's slug is its dropdown name in lowercase, with each run of other
characters as one `-`. Choosing an entry updates the address bar
(`history.replaceState`, so no history entries are added); editing the
fragment, or going back or forward, switches the entry. Saved edits apply as
for the dropdown (the AoC files open with their saved edits). An unknown
fragment opens the default example with a short notice beside the status. A
fragment is plain tokens only (letters, digits, `/`, `-`, `.`, `_`); it never
carries code.

**Not verified**: whether GitHub Pages compresses `.wasm` (§10.2 of the
playground note); check `content-encoding` on the real site with
`curl -I -H 'accept-encoding: gzip' https://mdr.github.io/stitchwort/pkg/stitchwort_web_bg.wasm`.
