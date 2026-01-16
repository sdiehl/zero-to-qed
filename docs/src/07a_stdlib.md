# Standard Library and Batteries

Lean's core library is intentionally minimal. The **Batteries** package extends it with data structures, utilities, and tactics that most projects need. This chapter surveys the most useful parts of Batteries and covers practical IO operations.

Add Batteries to your project in `lakefile.lean`:

```lean
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"
```

Or in `lakefile.toml`:

```toml
[[require]]
name = "batteries"
scope = "leanprover-community"
rev = "main"
```

## Data Structures

Batteries provides several data structures beyond the core library.

### BinaryHeap

A priority queue with \\(O(\log n)\\) insertion and extraction. Useful for scheduling, graph algorithms, and any problem requiring repeated min/max extraction.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:batteries_heap}}
```

The comparator determines ordering: `(· > ·)` for max-heap, `(· < ·)` for min-heap.

### RBMap and RBSet

Red-black tree maps and sets with \\(O(\log n)\\) operations and ordered iteration. Use when you need sorted keys or efficient range queries.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:batteries_rbmap}}
```

Unlike `HashMap`, iteration order is deterministic (sorted by key).

### UnionFind

Disjoint set data structure with near-constant time union and find operations. Essential for Kruskal's algorithm, connected components, and equivalence class problems.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:batteries_unionfind}}
```

### DList

Difference lists enable \\(O(1)\\) concatenation by representing lists as functions. Useful when building lists by repeated appending, which would be \\(O(n^2)\\) with regular lists.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:batteries_dlist}}
```

## Collection Extensions

Batteries extends `List`, `Array`, and `String` with additional operations.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:batteries_list_array}}
```

Other useful additions include `List.enum` (pairs elements with indices), `Array.swap` (exchange two elements), and various `String` utilities.

## IO Operations

The `IO` monad handles all side effects. The [Effects](./09_effects.md) chapter covers monads in depth; here we focus on practical operations.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:io_basics}}
```

### Files and Directories

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:file_io}}
```

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:directory_io}}
```

### External Processes

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:process_io}}
```

## Finding Packages

[Reservoir](https://reservoir.lean-lang.org/) indexes the Lean package ecosystem. Notable packages:

- **mathlib4**: Comprehensive mathematics library
- **aesop**: Proof automation via best-first search
- **lean4-cli**: Command-line argument parsing
- **Qq**: Quoted expressions for metaprogramming
- **ProofWidgets**: Interactive proof visualization

## Practical Example

A word frequency counter combining HashMap, String operations, and list processing:

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:practical_example}}
```
