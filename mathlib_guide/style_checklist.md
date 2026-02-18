# Mathlib Style Conventions Checklist

Use this checklist when writing or reviewing `.lean` files to ensure compliance with
mathlib style conventions. See [style.md](style.md) for full details and examples.

---

## Variable Naming

- [ ] Universes use `u`, `v`, `w`, ...
- [ ] Generic types use `α`, `β`, `γ`, ...
- [ ] Propositions use `a`, `b`, `c`, ...
- [ ] Elements of a generic type use `x`, `y`, `z`, ...
- [ ] Assumptions use `h`, `h₁`, `h₂`, ...
- [ ] Predicates and relations use `p`, `q`, `r`, ...
- [ ] Lists and sets use `s`, `t`, ...
- [ ] Natural numbers use `m`, `n`, `k`, ...
- [ ] Integers use `i`, `j`, `k`, ...
- [ ] Mathematical types use standard upper-case letters (`G` for group, `R` for ring, `K`/`𝕜` for field, `E` for vector space)

## Line Length

- [ ] All lines are at most 100 characters

## Header and Imports

- [ ] File begins with a copyright header (copyright year, author list, license)
- [ ] Author list uses `Authors:` (plural), no trailing period, comma-separated (no `and`)
- [ ] All `import` statements appear immediately after the header, with no blank line separating them
- [ ] Each `import` is on its own line

## Module Docstrings

- [ ] A module docstring (`/-! ... -/`) appears after the header and imports
- [ ] Docstring includes a title (`# ...`)
- [ ] Docstring includes a summary of contents (main definitions and theorems)
- [ ] Docstring includes notation used in the file (if any)
- [ ] Docstring includes references to literature (if any)

## Structuring Definitions and Theorems

- [ ] All declarations (`def`, `lemma`, `theorem`, `class`, `structure`, `instance`, etc.) are flush-left (not indented within namespaces/sections)
- [ ] All commands (`variable`, `open`, `section`, `namespace`, `notation`, etc.) are flush-left
- [ ] Spaces on both sides of `:`, `:=`, and infix operators
- [ ] Operators placed before a line break, not at the start of the next line
- [ ] Proof body indented by 2 spaces
- [ ] Multi-line theorem statements: subsequent lines indented by 4 spaces
- [ ] Multi-line theorem statements: proof still indented only 2 spaces (not 4+2)
- [ ] Short declarations on a single line when appropriate
- [ ] Parentheses not orphaned (kept with their arguments)

## `by` Placement

- [ ] `by` placed at the end of the preceding line (typically `:= by`), never on its own line
- [ ] Tactic block indented after `by`

## `have` Statements

- [ ] Short `have` justifications on the same line
- [ ] Long `have` justifications on the next line, indented by 2 additional spaces
- [ ] Tactic-mode `have` justifications: `by` on the same line as `have`

## Structure and Class Definitions

- [ ] Fields indented by 2 spaces
- [ ] Each field has a docstring (`/-- ... -/`)

## Instances

- [ ] `where` syntax used (no enclosing braces) when providing structure terms or class instances

## Hypotheses Placement

- [ ] Arguments placed left of the colon when the proof begins by introducing them
- [ ] Universal quantifiers / implications used right of the colon only when pattern-matching is involved

## Binders

- [ ] Space after binders (e.g., `∀ α : Type, ...`, `fun (x : α) ↦ ...`)

## Anonymous Functions

- [ ] `fun ... ↦ ...` preferred over `fun ... => ...` (use `↦` via `\mapsto`)
- [ ] `fun` keyword used instead of `λ` (which is disallowed in mathlib)
- [ ] Centered dot notation (`·`) used for simple functions where possible

## Calculations (`calc`)

- [ ] `calc` keyword placed at the end of the preceding line (like `by`)
- [ ] Relation symbols (`=`, `≤`, etc.) aligned across lines
- [ ] Continuation underscores `_` left-justified

## Tactic Mode

- [ ] New subgoals preceded by focusing dot `·`, not indented (but the tactic block after it is indented)
- [ ] One tactic per line (unless closing a goal on a single line or a short related sequence)
- [ ] `<;>` combinator: either on one line or the following tactic indented
- [ ] Very short side goals closed inline with `swap` or `pick_goal` to avoid extra indentation

## Squeezing `simp`

- [ ] Terminal `simp` calls are NOT squeezed (not replaced by `simp?` output), unless performance requires it

## Whitespace and Delimiters

- [ ] `<|` used instead of `$` for pipe-left
- [ ] Space after `←` in `rw` and `simp` calls (e.g., `rw [← add_comm a b]`)
- [ ] Space between tactic name and arguments (e.g., `rw [h]`, not `rw[h]`)
- [ ] Same spacing rules apply in `do` notation for `←`

## Empty Lines

- [ ] No empty lines inside declarations (use comments instead to annotate proof sections)
- [ ] Blank lines used to separate top-level declarations (may be omitted for short grouped definitions)

## Normal Forms

- [ ] Standard normal forms used in statements and conclusions (e.g., `s.Nonempty`, `(a : Option α)`)
- [ ] For `⊥`/`⊤` types: `x ≠ ⊥` in assumptions, `⊥ < x` in conclusions

## Comments and Documentation

- [ ] Module-level section headers use `/-! ... -/`
- [ ] Technical comments (TODOs, implementation notes) use `/- ... -/`
- [ ] Short inline comments use `--`
- [ ] Declaration docstrings use `/-- ... -/`
- [ ] Multi-line docstrings: subsequent lines are NOT indented

## Transparency and API Design

- [ ] Definitions are `semireducible` by default (no unnecessary `@[reducible]` or `@[irreducible]`)
- [ ] `abbrev` used only when `@[reducible]` is intentional
- [ ] No `erw` or `rfl` after `simp`/`rw` (indicates missing API lemmas)
- [ ] Structure wrappers preferred over `irreducible` for sealed API boundaries

## Deprecation

- [ ] Removed/renamed declarations have a `@[deprecated (since := "YYYY-MM-DD")]` alias
- [ ] `to_additive` declarations have deprecations on both additive and multiplicative versions

## Miscellaneous

- [ ] `nonrec` avoided when a namespace qualifier is more informative
- [ ] New bibliography entries added to `docs/references.bib`
