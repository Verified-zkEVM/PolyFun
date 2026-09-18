# Getting started

You can read PolyFun's definitions without running Lean. To edit a proof or
execute an example, install Lean and open a Lake project in your editor.
Lake is Lean's build system and dependency manager; `elan` selects the compiler
recorded in a project's `lean-toolchain` file.

## Install the tools

Follow the [Lean installation instructions](https://leanprover-community.github.io/get_started.html)
for your operating system. The usual setup is VS Code with the Lean 4 extension,
Git, and `elan`, which supplies Lean and Lake. Open the repository folder in
VS Code so the extension finds the project's toolchain and dependencies.

You do not need category theory to follow the [first program](tutorials/first-program.md).
For Lean syntax and proof basics, see [Learning Lean](https://leanprover-community.github.io/learn.html).

## Work in this repository

```sh
git clone https://github.com/Verified-zkEVM/PolyFun.git
cd PolyFun
lake exe cache get
lake build
lake build PolyFunExamples
```

The cache command downloads precompiled dependencies. The first build can still
take time to compile PolyFun. `lake build` builds the generic library; the final
command builds the optional tutorials. Open
[`Examples/Tutorials/Requests.lean`](../Examples/Tutorials/Requests.lean) and put
the cursor on its `example` to inspect Lean's proof state. A successful
check has no error; the editor marks any unfinished or invalid proof.

To check that file directly after building its imports:

```sh
lake env lean Examples/Tutorials/Requests.lean
```

To experiment without changing the tutorial, copy the README's Lean example into
`Main.lean` in the repository root and run `lake env lean Main.lean`.
`#eval` runs a computation; `example : ... := ...` checks a proof of its stated
property. The example's `rfl` proof succeeds because both sides compute to the
same value.

## Add PolyFun to your project

Start with a project using the same [`lean-toolchain`](../lean-toolchain) as the
PolyFun revision you select. For the current development API, add this to
`lakefile.toml`:

```toml
[[require]]
name = "PolyFun"
git = "https://github.com/Verified-zkEVM/PolyFun.git"
rev = "main"
```

The equivalent `lakefile.lean` declaration is:

```lean
require PolyFun from git "https://github.com/Verified-zkEVM/PolyFun.git" @ "main"
```

Then run:

```sh
lake update PolyFun
lake exe cache get
lake build
```

Commit the resulting `lake-manifest.json`: it records the resolved commit.
For a reproducible dependency declaration, replace `main` with that commit or
with a [release tag](https://github.com/Verified-zkEVM/PolyFun/releases) containing
the APIs you use. This documentation describes the source beside it. Older
releases may have different imports; read the documentation at the selected tag.
If your project also directly requires Mathlib or CSLib, align those revisions
with PolyFun's [`lakefile.toml`](../lakefile.toml).

Use specific imports while developing:

```lean
import PolyFun.PFunctor.Free.Basic
import PolyFun.PFunctor.Handler
```

`import PolyFun` makes the entire generic library available. The optional
`import PolyFunCslib` exposes concrete complexity adapters. Tutorials use
`import Examples.Tutorials.Requests`; their Lake target is `PolyFunExamples`.
These are distinct targets in one package, so depending on PolyFun does not
require building the optional examples or adapters.

## Choose your next step

- [First program and handlers](tutorials/first-program.md): write and interpret requests.
- [Computation models](guides/computation-models.md): choose programs, trees, or machines.
- [Indexed programs](tutorials/indexed-programs.md): make the interaction phase part of the type.
- [Repository map](reference/repo-map.md): find the right import and library root.
- [Validation](development/validation.md): checks to run before contributing.
