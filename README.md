# cubicaltt-scala

A Scala 3 implementation of [Cubical Type Theory](https://arxiv.org/abs/1611.02108) (CCHM), ported from Anders Mörtberg's [Haskell implementation](https://github.com/mortberg/cubicaltt). It is fully compatible with the original `.ctt` syntax and extends it with **metavariables** and **implicit arguments**.

The type theory is based on the paper:

> *Cubical Type Theory: a constructive interpretation of the univalence axiom*  
> Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg (2016)

---

## What is Cubical Type Theory?

Cubical Type Theory (CCHM) is a constructive type theory in which the user can directly manipulate *n*-dimensional cubes. It extends Martin-Löf type theory with:

- **Path types** — `PathP A a b` is the type of paths from `a` to `b` over a type family `A`
- **Path abstraction and application** — `<i> t` abstracts over a dimension; `p @ i` applies a path to a dimension
- **Composition and transport** — `comp`, `fill`, `transport` give a constructive account of Kan filling
- **Glue types** — `Glue`, `glue`, `unglue` allow equivalences to be turned into equalities, from which the **univalence axiom** is provable (not postulated)
- **Higher inductive types** — `hdata` declarations support path constructors with specified boundaries
- **Identity types** — `Id`, `idC`, `idJ` provide an alternative identity type with a definitional computation rule for `J`

Because composition is built in, many results that require axioms in book HoTT are directly provable here. For example, function extensionality holds by definition:

```
funExt (A : U) (B : A -> U) (f g : (x : A) -> B x)
       (p : (x : A) -> Path (B x) (f x) (g x)) :
       Path ((y : A) -> B y) f g = <i> \(a : A) -> (p a) @ i
```

---

## Extensions over the original

### Implicit arguments

Binders and applications support an implicit icity annotation using curly braces `{…}`. Implicit arguments are inferred by the elaborator via unification.

```
-- Declare an implicit binder
idfunI : {A : U} -> A -> A = \{A : U} (x : A) -> x

-- Implicit argument inferred from context
testId : Unit = idfunI tt

-- Explicit implicit argument via {expr} syntax
testExplicit : Unit = idfunI {Unit} tt
```

### Metavariables

Holes written as `_` in terms are elaborated into fresh metavariables. The elaborator attempts to solve them by unification during type checking. Unsolved metas are reported as errors.

```
-- The type of the hole is inferred
example : Path Unit tt tt = refl _ tt
```

The elaboration pipeline is:

```
Raw Term  ──parse+resolve──▶  Term (with Icity annotations)
          ──elaborate──▶      Term (metas solved, implicit args inserted)
          ──zonk──▶           Term (no remaining Meta nodes)
          ──TypeChecker──▶    ✓ well-typed
```

---

## Language reference

### Reserved keywords

```
module, where, let, in, split, with, mutual, import, data, hdata,
undefined, PathP, comp, transport, fill, Glue, glue, unglue, U,
opaque, transparent, transparent_all, Id, idC, idJ
```

### Types and terms

| Syntax | Meaning |
|---|---|
| `U` | Universe of types |
| `(x : A) -> B` | Dependent function type (Π) |
| `{x : A} -> B` | Implicit dependent function type |
| `\(x : A) -> t` | Lambda abstraction |
| `\{x : A} -> t` | Implicit lambda abstraction |
| `(x : A) * B` | Dependent pair type (Σ) |
| `(a, b)` | Pair |
| `t.1`, `t.2` | Projections |
| `PathP (<i> A) a b` | Path type (heterogeneous) |
| `Path A a b` | Homogeneous path (sugar for `PathP (<i> A) a b`) |
| `<i> t` | Path abstraction |
| `p @ i` | Path application |
| `comp (<i> A) a [(φ = 0) -> t, …]` | Composition |
| `fill (<i> A) a [(φ = 0) -> t, …]` | Fill |
| `transport (<i> A) a` | Transport |
| `Glue A [(φ = 0) -> (B, e), …]` | Glue type |
| `glue a [(φ = 0) -> b, …]` | Glue element |
| `unglue a [(φ = 0) -> (B, e), …]` | Unglue element |
| `Id A a b` | Identity type |
| `idC a` | Identity constructor (refl) |
| `idJ A a C d b p` | J eliminator |

### Declarations

```
-- Function definition with telescope
f (x : A) (y : B) : C = body

-- Recursive data type
data nat = zero | suc (n : nat)

-- Higher inductive type
data S1 = base | loop <i> [ (i=0) -> base, (i=1) -> base ]

-- Pattern matching
pred : nat -> nat = split
  zero  -> zero
  suc n -> n

-- Local definitions
f x = body where
  helper : T = ...

-- Mutual recursion
mutual
  even : nat -> bool = split ...
  odd  : nat -> bool = split ...

-- Opacity pragmas
opaque f
transparent f
transparent_all
```

### Face systems

Partial elements are written as systems `[(φ₁ = d₁) -> t₁, (φ₂ = d₂) -> t₂, …]` where `φᵢ` are dimension variables and `dᵢ ∈ {0, 1}`. Formulas support conjunction `i /\ j`, disjunction `i \/ j`, and negation `-i`.

---

## Build and install

Requires **Java 11+** and **sbt**.

```sh
sbt compile
```

To produce a fat JAR:

```sh
sbt assembly
```

Or run directly via sbt:

```sh
sbt run examples/demo.ctt
```

---

## Usage

```
cubicaltt [options] <file.ctt>

Options:
  --help     print help
  --version  print version
  -d         debug/verbose mode
  -b         batch mode (no REPL)
  -t         measure time
```

### Interactive REPL

When a file is loaded, an interactive loop is started. Available commands:

```
<statement>     infer type and evaluate statement
:n <statement>  normalize statement
:q              quit
:l <filename>   load filename (resets environment)
:r              reload current file
:h              display this message
```

---

## Examples

The `examples/` directory contains a library of `.ctt` files, including all examples from the original Haskell implementation plus new ones demonstrating the Scala extensions.

| File | Contents |
|---|---|
| `prelude.ctt` | Path types, `refl`, `funExt`, `trans`, propositions, sets |
| `demo.ctt` | Introductory tour of the system |
| `nat.ctt` | Natural numbers |
| `bool.ctt` | Booleans |
| `list.ctt` | Polymorphic lists |
| `list_implicit.ctt` | Lists using implicit arguments |
| `equiv.ctt` | Equivalences and `isoPath` |
| `univalence.ctt` | Proof of the univalence axiom |
| `circle.ctt` | The circle `S¹` as a HIT |
| `interval.ctt` | The interval as a HIT; funext from it |
| `idtypes.ctt` | Identity types |
| `hedberg.ctt` | Hedberg's theorem |
| `integer.ctt` | The integers |
| `pi.ctt` | Π-types |
| `sigma.ctt` | Σ-types |
| `torus.ctt` | The torus as a HIT |
| `groupoidTrunc.ctt` | Groupoid truncation |
| `propTrunc.ctt` | Propositional truncation |
| `category.ctt` | Category theory |
| `grothendieck.ctt` | Grothendieck construction |

---

## Running the tests

```sh
sbt test
```

Slow tests (e.g. `brunerie.ctt`) are excluded by default. To include them:

```sh
sbt 'set Test / testOptions := Seq()' "testOnly * -- -n Slow"
```

---

## Project structure

```
src/main/scala/cubical/
  Parser.scala          — .ctt parser (scala-parser-combinators)
  LayoutPreprocessor.scala — layout rule (indentation → braces)
  RawSyntax.scala       — unresolved AST produced by the parser
  Resolver.scala        — name resolution: strings → Names/SymKinds
  Syntax.scala          — resolved core term AST
  Elaborator.scala      — bidirectional elaborator (implicit insertion, metas)
  MetaContext.scala      — metavariable store (fresh, solve, zonk, force)
  Unify.scala           — unification for meta solving
  TypeChecker.scala     — core bidirectional type checker
  Eval.scala            — definitional equality, normalisation, composition
  Domain.scala          — semantic domain (Val, closures, environments)
  Connections.scala     — interval formula operations (∧, ∨, ¬, faces)
  Main.scala            — entry point and REPL
```

---

## References

- Cohen, Coquand, Huber, Mörtberg. [*Cubical Type Theory: a constructive interpretation of the univalence axiom*](https://arxiv.org/abs/1611.02108). TYPES 2015.
- Huber. [*Canonicity for Cubical Type Theory*](https://arxiv.org/abs/1607.04156).
- Coquand, Kinoshita, Nordström, Takeyama. [*A simple type-theoretic language: Mini-TT*](http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf).
- Mörtberg et al. [cubicaltt (Haskell)](https://github.com/mortberg/cubicaltt) — the original implementation this port is based on.
- The HoTT Book. [homotopytypetheory.org](https://homotopytypetheory.org/).

---

## Authors

Original Haskell implementation: Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg.

Scala port with metavariables and implicit arguments: this project.
