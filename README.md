- [This repository](#this-repository)
- [Lean 4](#lean-4)
  - [Brief history](#brief-history)
  - [Description](#description)
  - ["Basic" libraries](#basic-libraries)
  - [Resources](#resources)


# This repository

This repository contains material for the *anzenlang* Lean 4 training/introduction. It is released
under the Mozilla Public License v2.0, see [LICENSE](./LICENSE) for more details.

Participants learn Lean 4 by writing an interpreter for (an extended version of) the [brainfuck]
language. The material is not self-sufficient to properly present Lean 4, it requires a trainer
guiding participants and presenting/adding context to every step of the process.

See [resources](#resources) for standalone Lean 4 learning material, in particular [Functional
Programming in Lean][fpil].



# Lean 4

- [Lean 4 on wikipedia][wikipedia]



## Brief history

- 2013: [Leonardo de Moura][leo] "releases" Lean 1

  compiler mostly in `C++`

- 2017: Lean 3, first *"stable"* version, still (very) experimental

  compiler still mostly `C++`

- 2021: Lean 4, first stable version

  compiler (eventually) almost completely written in Lean 4

- 2023: creation of the [Lean FRO][fro] to improve Lean 4 scalability and usability



## Description

- purely functional language

- strong, dependent type system

- great development language, also a great **I**nteractive **T**heorem **P**rover (ITP)

- heavily inspired by ML, Coq, and Haskell

- modern: (Rust-)cargo-like environment, utf-8-friendly, extremely clean syntax

  - `elan`: toolchain manager, fork of Rust's `rustup`
  - `lake`: project manager, pure Lean but based on Rust's `cargo`

- *efficient*
  - compiles to `C`
  - very clever [reference-counting-like memory management][immutable beans]



## "Basic" libraries

The Lean 4 community provides three "basic" packages/libraries:

- `core`: historically, contained only what the Lean compiler needs

  now transitioning to being a minimal standard library

  <https://github.com/leanprover/lean4>

- `batteries` (formerly `std`/`std4`): development-oriented standard library

  augments `core` with bells and whistles

  <https://github.com/leanprover/std4>

- `mathlib4`/`mathlib`: ITP standard library

  augments `core` and `batteries` with mostly theoretical definitions

  results from algebra, category theory, ...

  <https://github.com/leanprover-community/mathlib4>

Documentation for these libraries available here:

- <https://leanprover-community.github.io/mathlib4_docs>



## Resources

- [homepage][lean]

- [Lean FRO][fro]

- [community website][comm], aggregates many resources including Lean's Zulip

Learning:

- Functional Programming in Lean (FPiL)

  <https://lean-lang.org/functional_programming_in_lean>

- Theorem-Proving in Lean (TPiL)

  <https://lean-lang.org/theorem_proving_in_lean4>

- Meta-Programming in Lean (MPiL)

  <https://leanprover-community.github.io/lean4-metaprogramming-book>

- Lean manual

  <https://lean-lang.org/lean4/doc>

- mathematics in Lean

  <https://leanprover-community.github.io/mathematics_in_lean/index.html>



[bf]: https://en.wikipedia.org/wiki/Brainfuck
[wikipedia]: https://en.wikipedia.org/wiki/Lean_(proof_assistant)
[leo]: https://leodemoura.github.io
[fro]: https://lean-fro.org
[comm]: https://leanprover-community.github.io
[immutable beans]: https://arxiv.org/pdf/1908.05647
[lean]: https://lean-lang.org
[fpil]: https://lean-lang.org/functional_programming_in_lean
