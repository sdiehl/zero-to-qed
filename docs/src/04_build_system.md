# Lake Build System

Every programming language eventually grows a build system, and that build system eventually grows into a small civilization with its own customs and territorial disputes. Lake is Lean's entry in this tradition. It borrows good ideas from Cargo, is written in Lean itself, and mostly works. The documentation is sparse, the error messages occasionally cryptic, and there are two competing configuration formats that do almost but not quite the same thing. Welcome to the frontier.

That said, Lake gets the job done. Paired with Elan for version management, you get reproducible builds and workable dependency management. Code that compiles on your machine will usually compile on other machines. For a young ecosystem, this is not nothing.

## Elan

Elan is the Lean version manager. It downloads, installs, and switches between different versions of Lean. Most users install Elan first and then let it manage their Lean installation. On Unix systems, installation is a single command that downloads and runs the installer script. On Windows, a dedicated installer is available.

Once installed, Elan reads a `lean-toolchain` file in your project directory to determine which Lean version to use. This file typically contains a single line specifying the version, such as `leanprover/lean4:v4.3.0` or simply `leanprover/lean4:stable` for the latest stable release. When you enter a directory containing this file, Elan automatically activates the correct version. If that version is not installed, Elan downloads it transparently.

This per-project versioning solves a common problem in software development. Different projects may require different Lean versions, and Elan lets them coexist without conflict. You can work on a project using Lean 4.2 in one terminal and a project using Lean 4.5 in another. The toolchain file checked into version control ensures all collaborators use the same Lean version.

Elan also manages additional toolchain components. The Lean installation includes the compiler, the language server for editor integration, and documentation tools. Updates happen through Elan with commands like `elan update` to fetch the latest versions.

## Lake

Lake is the build system and package manager for Lean. The name combines "Lean" and "Make," and every Lean project contains a `lakefile.lean` that describes its structure, dependencies, and build configuration. A minimal lakefile declares the package name and defines one or more build targets. The most common targets are libraries, which compile Lean source files into modules that other code can import, and executables, which produce standalone programs. Lake reads this configuration and orchestrates compilation, handling dependencies between modules automatically.

```lean
import Lake
open Lake DSL

package myproject where
  version := v!"0.1.0"

lean_lib MyLib where
  roots := #[`MyLib]

@[default_target]
lean_exe myapp where
  root := `Main
```

This lakefile defines a package named myproject containing a library called MyLib and an executable called myapp. The library compiles all modules under the MyLib namespace, while the executable uses Main as its entry point. The `@[default_target]` attribute marks myapp as the target built when you run `lake build` without arguments.

Dependencies on external packages are declared in the lakefile using the `require` keyword. Lake fetches dependencies from Git repositories, and you can specify versions through tags, branches, or commit hashes. When you build your project, Lake first ensures all dependencies are available and up to date, then compiles them before your own code. [Reservoir](https://reservoir.lean-lang.org/) serves as the community package registry, indexing Lean packages and providing searchable documentation, dependency graphs, and build status for the ecosystem.

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.3.0"

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "master"
```

Lake maintains a `lake-manifest.json` file that records the exact versions of all dependencies. This lockfile ensures reproducible builds across different machines and times. When you run `lake update`, Lake fetches the latest versions matching your constraints and updates the manifest.

The build process produces artifacts in a `.lake` directory within your project. Compiled Lean files become `.olean` files containing serialized proof terms and compiled code. These intermediate files enable incremental compilation, where Lake only recompiles modules that have changed or whose dependencies have changed. For large projects like Mathlib, this incremental approach is essential for practical development.

Lake also supports downloading precompiled artifacts called caches. Mathlib maintains a cache of compiled artifacts for anyone who would rather not spend hours rebuilding from source. The `lake exe cache get` command fetches these artifacts, reducing initial setup from hours to minutes.

## Project Structure

A typical Lean project follows a conventional directory layout. The lakefile sits at the project root alongside the lean-toolchain file. Source files live in directories matching their module namespaces. A module named `MyLib.Data.List` would be in the file `MyLib/Data/List.lean`. This correspondence between filesystem paths and module names makes navigation straightforward.

```
myproject/
  lakefile.lean
  lean-toolchain
  lake-manifest.json
  MyLib/
    Basic.lean
    Data/
      List.lean
      Vector.lean
  Main.lean
```

Test files typically live in a separate directory, often called `Test` or `Tests`, with their own library target in the lakefile. Documentation, examples, and scripts occupy other directories as needed. Lake does not enforce a particular structure beyond the lakefile requirements, but conventions have emerged from the community.

## Common Commands

Building a project uses `lake build`, which compiles all default targets. You can build specific targets by name, like `lake build MyLib` or `lake build myapp`. For development, `lake build` after editing a file recompiles only what changed.

Running an executable uses `lake exe` followed by the executable name, like `lake exe myapp`. Arguments after the executable name pass through to the program. You can also use `lake run` with the executable target name.

Managing dependencies uses `lake update` to refresh the manifest with the latest matching versions. After modifying the lakefile to add or change dependencies, running `lake update` fetches and locks the new versions.

Cleaning build artifacts uses `lake clean`, which removes the `.lake/build` directory.

The `lake env` command prints environment variables that configure Lean to find your project's modules. This is useful when running Lean directly or integrating with external tools.

## Editor Integration

The Lean language server provides IDE features like error highlighting, go-to-definition, type information on hover, and code completion. Lake integrates with the language server by providing project configuration. When you open a Lean file in an editor with Lean support, the language server reads your lakefile to understand the project structure.

Visual Studio Code with the lean4 extension is the most popular editor setup. The extension automatically starts the language server and provides a panel showing proof states and messages. Other editors like Emacs and Neovim have community-maintained Lean integrations that communicate with the same language server.

For the language server to work correctly, it must know about your project configuration. Opening a Lean file outside a Lake project, or opening a file before dependencies are built, can cause errors. Building the project with `lake build` before editing ensures the language server has the information it needs.

## The Interactive Workflow

Lean development is fundamentally interactive. Unlike batch compilers where you write code, compile, and hope for the best, Lean provides continuous feedback as you type. This tight feedback loop is not a convenience feature but the primary way you develop in Lean.

The **Infoview** panel is your window into Lean's reasoning. In VS Code, it appears on the right side when you open a Lean file. As you move your cursor through the code, the Infoview updates to show the state at that position. When writing proofs, it displays the current goal: what hypotheses you have available and what remains to be proved. When writing programs, it shows types and values. This panel is essential for understanding what Lean sees at every point in your code.

Consider a simple proof in progress:

```lean
theorem add_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero => simp
  | succ n ih => _
```

When your cursor is on the underscore, the Infoview shows:

```
case succ
m n : Nat
ih : n + m = m + n
⊢ n + 1 + m = m + (n + 1)
```

This goal state tells you everything: you are in the `succ` case of an induction, you have `m` and `n` as natural numbers, you have an induction hypothesis `ih`, and you must prove the equation shown after the turnstile `⊢`. Without this feedback, tactic proving would be like navigating a maze blindfolded.

## Evaluation Commands

Lean provides several commands that evaluate expressions and report results directly in the editor. These are invaluable for exploration and debugging.

**#check** displays the type of an expression:

```lean
#check 1 + 1        -- 1 + 1 : Nat
#check [1, 2, 3]    -- [1, 2, 3] : List Nat
#check fun x => x   -- fun x => x : ?m.1 → ?m.1
```

**#eval** evaluates an expression and shows its value:

```lean
#eval 2 + 2         -- 4
#eval [1, 2, 3].length  -- 3
#eval "hello".toUpper   -- "HELLO"
```

**#print** shows the definition of a constant, including theorems:

```lean
#print Nat.add_comm
-- theorem Nat.add_comm : ∀ (n m : Nat), n + m = m + n := ...
```

**#reduce** fully reduces an expression using definitional equality:

```lean
#reduce (fun x => x + 1) 5  -- 6
```

These commands appear as blue underlines in VS Code. Hover over them or check the Infoview to see results. They let you test ideas immediately without writing a full program or proof.

## Reading Error Messages

Lean's error messages are verbose but precise. They tell you exactly what went wrong, which is both a blessing and a curse for newcomers who may find the detail overwhelming.

A **type mismatch** error shows what was expected and what was provided:

```
type mismatch
  h
has type
  P
but is expected to have type
  Q
```

This means you tried to use a proof of `P` where a proof of `Q` was needed. Look at the goal state to understand what type you actually need.

An **unknown identifier** error means a name is not in scope:

```
unknown identifier 'foo'
```

Check for typos, missing imports, or hypotheses you forgot to introduce.

An **unsolved goals** error at the end of a proof means you have not proved everything:

```
unsolved goals
⊢ P ∧ Q
```

Your proof is incomplete. Look at what remains and continue.

The habit of reading error messages carefully, rather than guessing at fixes, will save hours of confusion. Lean is trying to help; let it.

## Mathlib Projects

Projects depending on Mathlib benefit from additional tooling. The `cache` executable bundled with Mathlib downloads prebuilt artifacts, avoiding the need to compile Mathlib yourself. After adding Mathlib as a dependency, running `lake exe cache get` fetches compiled files for your Lean version.

Mathlib projects often use a template that includes recommended configuration. The template sets up the toolchain file, lakefile, and auxiliary files for continuous integration and documentation generation. Starting from this template ensures compatibility with Mathlib's infrastructure.

Because Mathlib updates frequently, projects must balance using new features against the cost of keeping up with changes. Pinning to specific Mathlib versions provides stability, while tracking recent versions provides access to new material. The Mathlib changelog documents breaking changes to help with updates.

## Command Reference

| Command               | Description                             | Example                                     |
| --------------------- | --------------------------------------- | ------------------------------------------- |
| `lake new`            | Create a new project                    | `lake new myproject`                        |
| `lake init`           | Initialize project in current directory | `lake init myproject`                       |
| `lake build`          | Build default targets                   | `lake build`                                |
| `lake build <target>` | Build specific target                   | `lake build MyLib`                          |
| `lake clean`          | Remove build artifacts                  | `lake clean`                                |
| `lake clean --all`    | Remove artifacts and dependencies       | `lake clean --all`                          |
| `lake update`         | Update dependencies to latest versions  | `lake update`                               |
| `lake exe <name>`     | Run an executable                       | `lake exe myapp --flag`                     |
| `lake env`            | Print environment variables             | `lake env`                                  |
| `lake script run`     | Run a lakefile script                   | `lake script run test`                      |
| `lake test`           | Run project tests                       | `lake test`                                 |
| `lake exe cache get`  | Download Mathlib cache                  | `lake exe cache get`                        |
| `elan show`           | Show installed toolchains               | `elan show`                                 |
| `elan update`         | Update all toolchains                   | `elan update`                               |
| `elan default`        | Set default toolchain                   | `elan default leanprover/lean4:stable`      |
| `elan override`       | Set directory-specific toolchain        | `elan override set leanprover/lean4:v4.3.0` |

## Compiler Backend and Runtime

Lean 4 compiles to C code, which is then compiled to native executables using a system C compiler (typically Clang or GCC). This compilation pipeline differs from most theorem provers, which either interpret code or extract to another language like OCaml or Haskell. The choice to target C provides portability and enables linking with existing C libraries.

The compilation process involves several stages. Lean source code is first type-checked and elaborated into the Lean kernel language. Proof terms are then erased since they have no computational content. The remaining code is converted to an intermediate representation that resembles a simplified functional language. This intermediate form is then translated to C code that Lake compiles with your system's C compiler.

Lean's runtime uses reference counting rather than tracing garbage collection. Each heap-allocated object maintains a count of references to it. When the count drops to zero, the object is immediately freed. This approach has lower latency than tracing collectors since there are no garbage collection pauses. The [Counting Immutable Beans](https://arxiv.org/pdf/1908.05647) paper describes the design in detail.

Reference counting enables a technique the Lean developers call Functional But In-Place. When you perform a functional update on a data structure and the original has a reference count of one, the runtime can reuse the memory in place rather than allocating new storage. This means that pure functional code operating on unshared data achieves performance comparable to imperative mutation. The `Array` type in Lean exploits this property: appending to an unshared array mutates it in place despite the pure functional semantics.

The runtime is strict, not lazy like Haskell. All function arguments are evaluated before the function body executes. This makes performance more predictable but requires different idioms for infinite data structures or expensive computations that might not be needed. Lean provides explicit thunks via the `Thunk` type when lazy evaluation is required.

> [!CAUTION]
> The ecosystem lacks mature libraries for common tasks like HTTP clients, database connectors, encryption, and async I/O. While the [Axiomed](https://reservoir.lean-lang.org/@axiomed/Http) project is building HTTP support and the community has created socket bindings, these are far less polished than equivalents in established languages. Linking against system libraries requires out-of-band setup that Lake cannot manage portably across operating systems. Parallelism is supported in the form of cooperative scheduling on multiple threads.

Binary sizes tend to be large because the generated C code includes the Lean runtime and any Mathlib dependencies are substantial. Compile times for projects depending on Mathlib can be lengthy, though the cache system mitigates this for incremental builds. The compiler itself is under active development, with the [Year 3 Roadmap](https://lean-lang.org/fro/roadmap/y3/) promising improvements to code generation, smaller binaries, and better reference counting.

For production systems, Lean is best suited as a specification and verification tool rather than as the implementation language. A practical pattern is to write formal specifications in Lean, prove properties about algorithms, then implement the actual system in a production language while using Lean-generated tests or runtime checks to verify the implementation matches the specification. Alternatively, Lean excels for tools where correctness matters more than ecosystem maturity: proof automation, code generators, domain-specific languages, and programs where the type system's expressiveness justifies the ecosystem tradeoffs.
