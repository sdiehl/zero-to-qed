# Standard Library and Batteries

Lean's standard library (`Std`) provides essential data structures and utilities. The community **Batteries** package extends it further with additional data structures and algorithms. This chapter surveys the most useful parts of both.

## Std Data Structures

The `Std` namespace contains hash-based and tree-based collections that cover most common use cases.

### HashMap

Hash maps provide average \\(O(1)\\) insertion and lookup. Use them when key order doesn't matter.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:std_hashmap}}
```

### HashSet

Hash sets efficiently track membership without associated values.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:std_hashset}}
```

### TreeMap

Tree maps maintain keys in sorted order with \\(O(\log n)\\) operations. Use when you need ordered iteration or range queries.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:std_treemap}}
```

### Time

Basic timing operations are available through `IO`.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:std_time}}
```

For full date/time handling, the `Std.Time` module provides `DateTime`, `Duration`, and timezone support.

### Parsec

The `Std.Internal.Parsec` module provides parser combinators for building parsers from smaller pieces. It includes character-level parsers (`digit`, `asciiLetter`), repetition combinators (`many`, `many1`), and string building functions.

```lean
{{#include ../../src/ZeroToQED/StdLibrary.lean:std_parsec}}
```

For more advanced parsing needs, community libraries like [lean4-parser](https://github.com/fgdorais/lean4-parser) and [Megaparsec.lean](https://github.com/argumentcomputer/Megaparsec.lean) offer additional features.

## Batteries

The Batteries package provides additional data structures beyond Std. Add it to your project in `lakefile.lean`:

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

Batteries provides several data structures beyond Std.

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
