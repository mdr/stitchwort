# SW-3635: terminal colour audit and recommended palette

Paper lane, 16 Nov 2026. Preview: `preview.html` (same folder). Contrast ratios are WCAG 2 relative luminance, computed by script from the palettes' published RGB values (scripts in the parent scratch folder: `contrast.py`, `tbl.py`, `cube.py`).

## Recommendation in one paragraph

Stop using blue and make **operators bold in the default foreground**: it is visible on every background and palette because it uses the user's own text colour. Move the rest to **256-colour mid-tones** chosen so every colour has contrast of about 4.3:1 or more against both pure black and pure white (no theme detection, no light/dark switch). Keep the 16-colour set as the fallback for terminals without 256 colours. Bold is used for keywords, operators and errors, as the extra non-colour signal. Honour `NO_COLOR`; no dark/light switch for now.

## Proposed palette (REPL and error messages share it)

256-colour SGR is `38;5;N`. Hex is the xterm cube value of N.

| Class | SGR | Hex | on black / on white | Bold | Reason |
|---|---|---|---|---|---|
| keyword | `1;38;5;163` | #d700af | 4.5 / 4.7 | yes | magenta is the only 16-colour hue that is mid-contrast on both backgrounds; keeps today's hue; bold marks it as structure |
| operator | `1` | default fg | 21 / 21 | yes | Matt's blue complaint; the default foreground cannot be hard to see; bold gives it weight against names |
| number | `38;5;130` | #af5f00 | 4.5 / 4.7 | no | orange-brown, distinct from green and teal; replaces cyan (poor on white) |
| text (strings) | `38;5;28` | #008700 | 4.5 / 4.7 | no | green stays the string colour (ptpython, Pygments default and Ammonite also use green) |
| capitalised names, types | `38;5;30` | #008787 | 4.8 / 4.4 | no | teal; replaces yellow (1.7 to 3.0 on white) |
| type shown after a result | `38;5;30` | #008787 | 4.8 / 4.4 | no | same as types |
| comment | `38;5;243` | #767676 | 4.6 / 4.5 | no | a grey that reads on both; today's 90 is the theme's "bright black", 3.7 to 5.2 on black, 1.0 on Solarized Dark; comments begin with the comment marker too, so colour is not the only signal |
| prompt | `2` | dim | n/a | no | not semantic; keep |
| error label, `Error:` | `1;38;5;196` | #ff0000 | 5.3 / 4.0 | yes | red, bold; on black today's 31 is 2.4 to 4.1 |
| warning | `1;38;5;130` | #af5f00 | 4.5 / 4.7 | yes | yellow is unreadable on white; bold orange |
| goal label | `38;5;30` | #008787 | 4.8 / 4.4 | no | teal for cyan |
| secondary label | `38;5;98` | #875fd7 | 4.7 / 4.5 | no | replaces ariadne's Blue; violet reads on both |
| diff highlight, mismatches | bold + underline, `38;5;28` (expected) / `38;5;196` (found) | | | yes | already not colour-only (bold and underline) |
| `try:` | `1;38;5;28` | | | yes | as today with the new green |

Colour is never the only signal: operators, keywords and errors are bold; diff spans are underlined; ariadne's carets, `╰──` connectors and the text of each label carry the meaning without colour; comments carry their marker.

Contrast of the same colours on other backgrounds (the honest cost of fixed colours): on VS Code's own `#1e1e1e` background 3.1 to 4.2; on Solarized Dark (#002b36) 3.2 to 3.8; on Solarized Light (#fdf6e3) 3.7 to 4.4. All stay above the 3:1 WCAG threshold for large text and UI components, but not all above 4.5. The 16-colour ANSI route would instead follow the user's palette (fish's default theme, bat's `ansi` theme and ptpython's default style do that on purpose, see sources), but the tables below show the 16 colours are poor on one or other background in every palette tested.

Fallback when the terminal has no 256 colours (no `256color` in `TERM` and no `COLORTERM`): keyword `1;35`, operator `1`, number `36`, text `32`, names and types `33`, comment `90`, error `1;31`, warning `1;33`, goal `36`, secondary `35`. This is dark-background oriented; it drops the blue.

NO_COLOR and switches: honour `NO_COLOR` (non-empty value disables colour, per no-color.org; CPython 3.13 checks it before `FORCE_COLOR`); also off when stdout is not a terminal or `TERM=dumb`. A user flag or config setting should override `NO_COLOR` (no-color.org). No dark/light switch and no background detection are needed with this palette. If Matt later wants a theme override, the cheap form is one environment variable (for example `STITCHWORT_COLORS=16|256|off`), not a dark/light pair.

## Today's colours against black and white (16-colour, per palette)

Normal and bright variants of every colour used today (31 to 36, 90) plus the bright set. Each cell: contrast on black / on white. 4.5 is the WCAG AA threshold for normal text, 3 for large text.

| SGR | xterm: on black / on white | Terminal.app: on black / on white | iTerm2 default: on black / on white | VS Code Dark+: on black / on white |
|---|---|---|---|---|
| 31 red | 3.6 / 5.8 | 2.4 / 8.9 | 3.6 / 5.8 | 4.1 / 5.1 |
| 32 green | 9.7 / 2.2 | 6.5 / 3.3 | 8.7 / 2.4 | 8.5 / 2.5 |
| 33 yellow | 12.3 / 1.7 | 6.9 / 3.0 | 11.3 / 1.9 | 15.5 / 1.4 |
| 34 blue | 2.2 / 9.4 | 1.6 / 12.8 | 2.1 / 9.9 | 4.3 / 4.9 |
| 35 magenta | 4.5 / 4.7 | 3.5 / 5.9 | 4.8 / 4.4 | 4.6 / 4.6 |
| 36 cyan | 10.6 / 2.0 | 7.1 / 3.0 | 9.8 / 2.1 | 7.5 / 2.8 |
| 90 bright black | 5.2 / 4.0 | 3.7 / 5.7 | 3.8 / 5.6 | 3.7 / 5.7 |
| 91 bright red | 5.3 / 4.0 | 4.4 / 4.8 | 7.7 / 2.7 | 5.9 / 3.6 |
| 92 bright green | 15.3 / 1.4 | 10.9 / 1.9 | 15.4 / 1.4 | 10.6 / 2.0 |
| 93 bright yellow | 19.6 / 1.1 | 15.7 / 1.3 | 19.4 / 1.1 | 18.0 / 1.2 |
| 94 bright blue | 4.4 / 4.7 | 2.4 / 8.6 | 5.4 / 3.9 | 6.2 / 3.4 |
| 95 bright magenta | 6.7 / 3.1 | 5.5 / 3.8 | 9.3 / 2.2 | 7.1 / 2.9 |
| 96 bright cyan | 16.7 / 1.3 | 13.5 / 1.6 | 17.0 / 1.2 | 9.0 / 2.3 |

| SGR | Solarized: on base03 / on base3 |
|---|---|
| 31 red | 3.2 / 4.3 |
| 32 green | 4.7 / 3.0 |
| 33 yellow | 4.7 / 3.0 |
| 34 blue | 4.1 / 3.4 |
| 35 magenta | 3.3 / 4.2 |
| 36 cyan | 4.8 / 2.9 |
| 90 bright black | 1.0 / 13.9 |
| 91 bright red | 3.3 / 4.3 |
| 92 bright green | 2.8 / 5.0 |
| 93 bright yellow | 3.4 / 4.1 |
| 94 bright blue | 4.7 / 2.9 |
| 95 bright magenta | 3.4 / 4.1 |
| 96 bright cyan | 5.6 / 2.5 |

Reading it: **34 blue on black is 2.2 (xterm), 1.6 (Terminal.app), 2.1 (iTerm2)**, which is below even the 3:1 large-text threshold; only VS Code's lighter blue reaches 4.3. Blue is good on white (9 to 13). Yellow, green and cyan are the mirror image: 7 to 12 on black and 1.7 to 3.3 on white. Magenta (35) is the only normal colour that stays at 3.5 to 5.9 on both. Bright black (90, comments) is 3.7 to 5.2 on black and 4.0 to 5.7 on white in the plain palettes, but exactly the background colour (1.0) on Solarized Dark.

Terminal.app values are Wikipedia's "Terminal.app" column, which may not match a customised profile. VS Code values are the Dark+ debug-console palette from the same table, tested here against pure black and white, not its real #1e1e1e background.

### 256-colour candidates (contrast against pure black and pure white)

Best colours of the xterm 6x6x6 cube (indices 16 to 231) by lowest of the two contrasts (from `cube.py`): 63 #5f5fff 4.57, 29 #00875f 4.53, 98 #875fd7 4.52, 163 #d700af 4.51, 28 #008700 4.47, 130 #af5f00 4.46, 30 #008787 4.36, 196 #ff0000 4.00. Greyscale 243 (#767676) is 4.62 on black and 4.54 on white. A colour near luminance 0.18 is the best a single colour can do against both extremes: about 4.58 each side.

## Bold in common terminals

- xterm: bold text can be shown as a bright colour instead of a heavier font; xterm's `colorBDMode` resource ("enabling the display of characters with bold attribute as color rather than bold") and the Wikipedia article: "Quite a few terminals implemented 'bold' (SGR code 1) as a brighter color rather than a different font."
- iTerm2: has a "bold" colour and a setting that brightens bold text (its plist key is `Brighten Bold Text`); users untick it for 16-colour palettes such as Solarized so bold text does not override the palette. I could not confirm the factory default from a source.
- Terminal.app: Profiles > Text > "Use bright colors for bold text" (Apple's Terminal guide). The default for the Basic profile was not confirmed from a source. Per-profile.
- Effect: bold + 31..37 may become 91..97 in some setups, so bold red on black goes from 3.6 to 5.3 (xterm), a benefit on dark and a loss on white (5.8 to 4.0). Bold + 38;5;N (256-colour) is not affected by this brightening in xterm-like terminals, I believe, but I did not find a source for that, so check in Matt's terminal.
- Practical consequence: bold is a safe addition when the base colour is the default foreground (operators) or a 256-colour (no palette brightening), and when it is the only change. Python 3.13's REPL uses bold blue for keywords, relying on this behaviour.

## What the good REPLs and highlighters do

| Tool | Per-token colours | Bold | Colour depth | Light/dark |
|---|---|---|---|---|
| ptpython (default ANSI style) | comment italic bright black; keyword **bold green**; operator bright black; string red; number bright black; function name bright blue, variable blue, builtin green | keyword | 16 named ANSI colours | no switch; comment in the source: ANSI names "adapt better to light/dark mode"; other Pygments styles use RGB |
| IPython (`neutral` theme, 9.x) | Pygments `default` style as base (keyword bold #008000 green, string #BA2121, number #666666, comment italic #3D7B7B, operator #666666) with ANSI overrides: number green, string yellow, class and namespace bold blue, function blue | class/namespace names, prompt numbers | ANSI names | themes by name: `neutral` (default on posix), `linux` (Monokai, for dark; the default on Windows because neutral is "not very visible on a dark background"), `lightbg` |
| bpython | keyword yellow, name cyan, comment blue, string magenta, number bold green, operator bold yellow, paren bold red | upper-case letters in its config | 8 base colours | theme files |
| Ammonite (Scala) | prompt magenta, identifiers cyan, types green, literals green, prefix yellow, comment blue, keyword yellow, error red, warning yellow, info blue, selected reversed | none (reverse for selection) | 16 ANSI (via fansi) | one default; `BlackWhite` set with all attrs empty for no colour |
| CPython 3.13 REPL | prompt bold magenta, keyword bold blue, builtin cyan, comment red, string green, number yellow, operator reset (default), definition bold | keywords, prompt, definitions | 16 ANSI | none; honours NO_COLOR, FORCE_COLOR, `TERM=dumb` |
| fish (default theme, "terminal colors") | autosuggestion bright black, comment red, error bright red, parameter cyan, quote yellow, operator and escape bright cyan, redirection cyan bold, valid path underlined | redirection, search match | 16 named terminal colours | one theme that follows the terminal's palette; other themes via `fish_config` |
| bat | default `Monokai Extended` (dark) or `Monokai Extended Light`, chosen automatically from the terminal background; `ansi` theme "looks decent on any terminal", 3-bit colours | by theme | truecolor if `COLORTERM` says so, else 8-bit | auto-detects background; `--theme-dark`/`--theme-light` |

Patterns to note: nobody uses blue for operators; the common choices for operators are bright black (ptpython), the default colour (CPython, Pygments' operator is grey), or bold yellow (bpython). Bold goes on keywords, definitions and prompts, not on every token. ANSI-name palettes (ptpython, fish, bat `ansi`, IPython neutral) rely on the user's terminal theme; the tools that auto-select a light or dark theme (bat) detect the background. Comments are blue (Ammonite, bpython) or red (CPython, fish): they are not always grey.

## Sources (all fetched 16 Nov 2026)

- ptpython `src/ptpython/style.py`: https://raw.githubusercontent.com/prompt-toolkit/ptpython/main/src/ptpython/style.py
- IPython themes: https://raw.githubusercontent.com/ipython/ipython/main/IPython/utils/themes/neutral-posix.json and `linux.json` (same folder); `IPython/utils/PyColorize.py` (theme table and the Windows comment): https://raw.githubusercontent.com/ipython/ipython/main/IPython/utils/PyColorize.py ; `IPython/terminal/interactiveshell.py`
- Pygments default style: https://raw.githubusercontent.com/pygments/pygments/master/pygments/styles/default.py
- bpython `bpython/config.py` (default colour letters; the meaning of upper case as bold is my reading of the default scheme, the file does not state it): https://raw.githubusercontent.com/bpython/bpython/main/bpython/config.py
- Ammonite `Colors` in `amm/util/src/main/scala/ammonite/util/Model.scala` at commit c8804698: https://github.com/com-lihaoyi/Ammonite/blob/c8804698996a98dcef71ad738f31f870c7716d36/amm/util/src/main/scala/ammonite/util/Model.scala
- CPython `Lib/_colorize.py`: https://raw.githubusercontent.com/python/cpython/main/Lib/_colorize.py
- fish interactive docs (variables, modifiers): https://fishshell.com/docs/current/interactive.html ; default theme: https://raw.githubusercontent.com/fish-shell/fish-shell/master/share/themes/default.theme (summarised by the fetch tool, not read verbatim)
- bat README: https://raw.githubusercontent.com/sharkdp/bat/master/README.md
- Palette values: https://en.wikipedia.org/wiki/ANSI_escape_code (raw wikitext table: xterm, Terminal.app, VS Code Dark+, and the quote on bold); iTerm2 Default and Light Background presets: https://raw.githubusercontent.com/mbadolato/iTerm2-Color-Schemes/master/alacritty/iTerm2%20Default.toml ; Solarized: https://ethanschoonover.com/solarized/
- Bold settings: xterm manual https://invisible-island.net/xterm/manpage/xterm.html (colorBDMode); Apple Terminal text preferences https://support.apple.com/en-gb/guide/terminal/trmltxt/mac (found by search, not fetched in full); iTerm2 colours doc https://iterm2.com/documentation-preferences-profiles-colors.html (no mention of the brighten setting)
- NO_COLOR: https://no-color.org/
- WCAG contrast formula: standard relative luminance (WCAG 2); computed locally, not fetched.

## Not verified

iTerm2 and Terminal.app factory defaults for bold-as-bright; whether bold + 256-colour is ever brightened; IPython's pre-9.x default style (the repo's current themes were read); exact content of fish's default.theme; bpython's meaning of upper-case letters.
