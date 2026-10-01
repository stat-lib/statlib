# Statlib

[![Build and lint](https://github.com/stat-lib/statlib/actions/workflows/ci.yml/badge.svg)](https://github.com/stat-lib/statlib/actions/workflows/ci.yml)
[![Apache 2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)


Statlib is an open community that aims to support the verification of classical, contemporary, and emerging research in mathematical statistics; its vision and goals are shaped by the whole community. We build with [Institute for Computer-Aided Reasoning in Mathematics (ICARM)](https://icarm.io/) at CMU. 

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
behavior should be discussed.

For a substantial new formalization or API, our workflow is:

1. **Open an issue.** 
2. **Discuss the design specification in the issue.** 
3. **Implement with/after the design direction is clear.** 
4. **Open a pull request linked to the issue.** 

You may find a proposed (not mandetary) form in [design document template](roadmap/README.md). Small fixes, documentation improvements, and narrowly scoped lemmas do not need a full design document. 

Not sure what to do? You may also find a list of todo [here](https://stat-lib.github.io/todos.html) 

Any question? Please comment in [Statlib Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/611809-Statlib).

## Using AI

We understand people have different opinions of AI. Feel free to use AI effectively, but remember that the goal is to make things readable and clear for human to engage with the materials.


## License

Statlib is released under the [Apache License 2.0](LICENSE).
