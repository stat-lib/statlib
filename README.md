# Statlib

[![Build and lint](https://github.com/stat-lib/statlib/actions/workflows/ci.yml/badge.svg)](https://github.com/stat-lib/statlib/actions/workflows/ci.yml)
[![Apache 2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Statlib is a community-developed Lean 4 library for mathematical statistics. It builds on
[Mathlib](https://github.com/leanprover-community/mathlib4) to develop reusable statistical
definitions, theorems, and research infrastructure.

Statlib is research-driven: its mathematical scope and APIs are developed jointly by statisticians
and Lean contributors. The project is under active development.

[Website](https://stat-lib.github.io/) ·
[Tutorial](https://stat-lib.github.io/tutorial/) ·
[API documentation](https://stat-lib.github.io/docs/) ·
[Roadmap](https://stat-lib.github.io/roadmap.html) ·
[Contributing guide](https://stat-lib.github.io/contribute.html) ·
[Zulip](https://leanprover.zulipchat.com/#narrow/channel/611809-Statlib)

## Design before code

A coherent library is more than a collection of independently formalized results. Definitions and
theorem statements establish vocabulary and conventions that later code will depend on. Choices
such as names, namespaces, representations, parameter order, typeclass assumptions, and boundary
behavior are expensive to change once a large API has been built around them.

For a substantial new formalization or API, our workflow is:

1. **Open an issue.** Describe the mathematical source, intended scope, central definitions and
   results, and the parts of Mathlib or Statlib that the work should build on.
2. **Discuss the design specification in the issue.** Contributors should reach a shared direction
   for the mathematical representation, level of generality, naming and code conventions, file
   organization, and compatibility with Mathlib.
3. **Implement after the design direction is clear.** If implementation reveals that a design
   choice should change, bring that decision back to the issue. The discussion remains the public
   record and gives reviewers context for the resulting code.
4. **Open a pull request linked to the issue.** Keep the change reviewable and explain any departure
   from the agreed design.

This discussion is especially important before manually writing or generating a large amount of
code. Early agreement prevents incompatible parallel APIs, avoids locking in accidental naming or
representation choices, and makes later review and maintenance substantially easier.

The proposed [design document template](roadmap/README.md) is a reference checklist, not a required
form. Use the sections that help clarify the project; the design discussion itself happens in the
GitHub issue.

Small fixes, documentation improvements, and narrowly scoped lemmas do not need a full design
document. When in doubt, open an issue or ask in the
[Statlib Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/611809-Statlib).

## Current areas

The library currently includes work on:

- causal inference and potential responses;
- contiguity and local asymptotic theory;
- E-values and E-variables;
- quadratic mean differentiability and statistical inference;
- supporting measure-theoretic results intended for eventual contribution to Mathlib.

See the [API documentation](https://stat-lib.github.io/docs/) for the current module tree and the
[roadmap](https://stat-lib.github.io/roadmap.html) for longer-term directions.

## Build Statlib

Install Lean using [elan](https://lean-lang.org/install/), then clone and build the repository:

```sh
git clone https://github.com/stat-lib/statlib.git
cd statlib
lake exe cache get
lake build
```

A Lean file can import the whole library or an individual module:

```lean
import Statlib
import Statlib.Contiguity.Def
```

## Contributing

To propose a substantial project, start with a
[GitHub issue](https://github.com/stat-lib/statlib/issues/new/choose) and discuss its design before
opening a large code contribution. For pull-request expectations, the relationship with Mathlib,
and the project's policy on AI-assisted code, read the
[contributing guide](https://stat-lib.github.io/contribute.html).

Statlib follows the
[Mathlib style guide](https://leanprover-community.github.io/contribute/style.html) by default.
Contributors are responsible for understanding, explaining, and maintaining every line they submit,
regardless of which tools were used to produce it.

## License

Statlib is released under the [Apache License 2.0](LICENSE).
