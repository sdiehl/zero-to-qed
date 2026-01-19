# Appendix B: Toplevel Declarations

Every Lean file is a sequence of toplevel declarations. These are the building blocks of every program and proof. This appendix provides a quick reference for all declaration types, with links to detailed explanations in the main text.

## Definitions and Proofs

| Declaration   | Purpose                                | Example                                                   |
| ------------- | -------------------------------------- | --------------------------------------------------------- |
| **`def`**     | Define a value or function             | [Basics](./04_basics.md#zero)                             |
| **`theorem`** | State and prove a proposition (opaque) | [Basics](./04_basics.md#zero), [Proving](./12_proving.md) |
| **`lemma`**   | Same as `theorem`                      | [Proving](./12_proving.md)                                |
| **`example`** | Anonymous proof (not saved)            | [Type Theory](./13_type_theory.md)                        |
| **`abbrev`**  | Transparent abbreviation               | [Basics](./04_basics.md#more-declarations)                |
| **`opaque`**  | Hide implementation                    | [Proofs](./12_proving.md#axioms-and-escape-hatches)       |
| **`axiom`**   | Unproven assumption                    | [Proofs](./12_proving.md#axioms-and-escape-hatches)       |

The distinction between `def` and `theorem` matters for performance. Lean marks theorem proofs as opaque, meaning they are never unfolded during type checking. This keeps proof terms from bloating computations. Use `def` for values you need to compute with and `theorem` for propositions you need to prove.

## Type Declarations

| Declaration     | Purpose                        | Example                                                                      |
| --------------- | ------------------------------ | ---------------------------------------------------------------------------- |
| **`inductive`** | Define type with constructors  | [Data Structures](./06_data_structures.md#inductive-types)                   |
| **`structure`** | Single-constructor with fields | [Data Structures](./06_data_structures.md#structures)                        |
| **`class`**     | Type class interface           | [Polymorphism](./09_polymorphism.md#defining-type-classes)                   |
| **`instance`**  | Type class implementation      | [Polymorphism](./09_polymorphism.md#polymorphic-instances)                   |
| **`mutual`**    | Mutually recursive definitions | [Dependent Types](./14_dependent_types.md#mutual-and-nested-inductive-types) |

## Organization

| Declaration      | Purpose                  | Example                                                    |
| ---------------- | ------------------------ | ---------------------------------------------------------- |
| **`import`**     | Load another module      | [Basics](./04_basics.md#modules-and-namespaces)            |
| **`variable`**   | Auto-add to definitions  | [Basics](./04_basics.md#modules-and-namespaces)            |
| **`namespace`**  | Group under prefix       | [Basics](./04_basics.md#modules-and-namespaces)            |
| **`section`**    | Scope for variables      | [Basics](./04_basics.md#modules-and-namespaces)            |
| **`open`**       | Bring names into scope   | [Basics](./04_basics.md#modules-and-namespaces)            |
| **`universe`**   | Declare universe levels  | [Type Theory](./13_type_theory.md#universe-stratification) |
| **`attribute`**  | Attach metadata          | [Polymorphism](./09_polymorphism.md#attributes)            |
| **`export`**     | Re-export from namespace | [Basics](./04_basics.md#modules-and-namespaces)            |
| **`notation`**   | Custom syntax            | [Dependent Types](./14_dependent_types.md#custom-notation) |
| **`set_option`** | Configure compiler       | [Type Theory](./13_type_theory.md#compiler-options)        |

## Interactive Commands

| Command       | Purpose                | Example                                    |
| ------------- | ---------------------- | ------------------------------------------ |
| **`#eval`**   | Evaluate and print     | [Basics](./04_basics.md#zero)              |
| **`#check`**  | Display type           | [Basics](./04_basics.md#more-declarations) |
| **`#print`**  | Print declaration info | [Basics](./04_basics.md#more-declarations) |
| **`#reduce`** | Reduce to normal form  | [Basics](./04_basics.md#more-declarations) |

These commands are prefixed with `#` to distinguish them from regular declarations. They produce output but do not contribute to the compiled program. Use them liberally during development to inspect types and evaluate expressions.
