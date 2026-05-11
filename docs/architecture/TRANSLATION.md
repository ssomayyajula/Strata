# Translation: Python AST → Laurel AST

---

## Purpose

This document specifies the Translation pass of the pipeline. It is
companion material to `ARCHITECTURE.md` (prose overview) and
`ELABORATION.md` (the Laurel → GFGL pass that consumes Translation's
output).

Translation is not a typing system. Python has no static typing
derivation, so there is no derivation-tree correspondence between
Translation's input and output. The pass is an AST-to-AST fold over
Python source, specified below as a plain two-column desugaring
table. Each row rewrites a Python construct into its Laurel image.

Translation consults `Γ = TypeEnv` (built by Resolution) for name
lookups, signatures, kwargs resolution, class fields, and the
builtins map. It does not read grades; it does not insert coercions;
it does not determine effects — those are elaboration's concerns.

Recursion is implicit in the tables: every sub-expression of the LHS
is assumed to have been translated first and appears as its
Laurel-side image on the RHS. Lowercase `e`, `ex`, `ei`, `em`, `ec`
etc. on the RHS denote "the translation of the correspondingly-named
Python sub-expression". Lowercase `ss`, `ssb`, `sst`, `ssf`, `ssᵢ` on
the RHS denote the translation of the correspondingly-named Python
statement block.

---

## Expressions

| Python                              | Laurel                                                                                           |
|-------------------------------------|--------------------------------------------------------------------------------------------------|
| `n` (int literal)                   | `LiteralInt n`                                                                                   |
| `b` (bool literal)                  | `LiteralBool b`                                                                                  |
| `s` (str literal)                   | `LiteralString s`                                                                                |
| `x` (identifier)                    | `Identifier x`                                                                                   |
| `p₁ op p₂`                          | `StaticCall (opPrelude op) [e₁, e₂]`                                                             |
| `f(p₁,…,pₙ, kw=…)` with `f ∈ Γ`     | `StaticCall f args`, where `args = resolveKwargs(f, pos, kw)`                                    |
| `f(…)` with `f ∉ Γ`                 | `Hole` (nondeterministic — args discarded)                                                       |
| `recv.m(p₁,…,pₙ)`                   | `StaticCall (resolveMethodName recv m) [e_self, e₁,…,eₙ]`                                        |
| `recv.f`                            | `FieldSelect e_obj f`                                                                            |
| `Foo(p₁,…,pₙ)`  (class callee)      | handled at statement level — see `v = Foo(…)` in Statements                                      |
| `f"…{p₁}…{pₙ}…"`                    | `StaticCall to_string_any [concat …]`                                                            |
| `[p₁,…,pₙ]`                         | `from_ListAny (ListAny_cons e₁ … (ListAny_nil))`                                                 |
| `{k₁:v₁,…,kₙ:vₙ}`                   | `from_DictStrAny (DictStrAny_cons K₁ V₁ … empty)`                                                |
| `x[i]`                              | `Any_get(ex, ei)`                                                                                |
| `x[start:stop]`                     | `Any_get(ex, from_Slice(Any..as_int!(es), OptSome(Any..as_int!(et))))`                           |
| `x[start:]`                         | `Any_get(ex, from_Slice(Any..as_int!(es), OptNone()))`                                           |

## Statements

Each row translates the LHS Python statement to the RHS Laurel
statement list. Semicolons in the RHS separate statements within the
list.

| Python                                    | Laurel                                                                                                               |
|-------------------------------------------|----------------------------------------------------------------------------------------------------------------------|
| `x = p`                                   | `Assign [x] e`                                                                                                       |
| `x += p`                                  | `Assign [x] (PAdd x v)`                                                                                              |
| `a, b = rhs`                              | `tmp := e; a := Get(tmp, 0); b := Get(tmp, 1)`  (fresh `tmp`)                                                        |
| `x[i] = v`                                | `Assign [x] (Any_sets (ListAny_cons ei ListAny_nil) x ev)`                                                           |
| `return p`                                | `LaurelResult := e; exit $body`                                                                                      |
| `if cond: thn else: els`                  | `if ec then sst else ssf`                                                                                            |
| `while cond: body`                        | `while ec do ssb`                                                                                                    |
| `for x in iter: body`                     | `label $brk { label $cont { x := Hole; Assume (PIn x ei); ssb } }`  (fresh `$brk`, `$cont`, `x`)                     |
| `break`                                   | `exit $brk`  (current loop's break label)                                                                            |
| `continue`                                | `exit $cont`  (current loop's continue label)                                                                        |
| `with mgr as v: body`                     | `v := T@__enter__(em); ssb; T@__exit__(em)`  (`T = varType(mgr)`)                                                    |
| `try: body except Eᵢ: handlerᵢ`           | `maybe_except : Error := default; label $try { ssb }; if isError(maybe_except, Eᵢ) then ssᵢ else …`  (fresh `$try`) |
| `assert cond`                             | `Assert ec`                                                                                                          |
| `v = Foo(p₁,…,pₙ)`  (class `Foo`)         | `Assign [tmp] (New C); StaticCall Foo@__init__ [tmp, e₁,…,eₙ]; Assign [v] tmp`  (fresh `tmp`)                        |

## Module- and function-level declarations

Procedures and type definitions, rather than single statements.

| Python                                            | Laurel                                                                                                                                       |
|---------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------|
| `def f(params) → R: body`                         | `procedure f (pᵢ : Tᵢ) → (LaurelResult : R, maybe_except : Error) { scopeDecls; paramCopies; ssb }`                                          |
| `class C: body`  (fields `fᵢ : Tᵢ`, methods `mⱼ`) | `typedef C { compositeFields = (fᵢ : Tᵢ) }` + one top-level procedure per method, with `self : C` prepended to its params                    |
| module (top-level `stmts`)                        | `Program { staticProcedures = collectNestedDefs(stmts) ++ [ __main__ { topLevel(stmts) } ] }`  (`__main__` carries `sourceRangeToMd` metadata) |

### Function-body preprocessing

Before emitting a function's `ssb`, the fold performs:

- **scope hoisting** — collect every name assigned anywhere in the
  body, emit a `LocalVariable` declaration for each at the top of the
  body (Python's late-binding semantics made explicit in Laurel).
- **mutable param copies** — for each parameter `p` mutated in the
  body, emit a fresh local at body entry copied from `p`; rewrite
  mutations to target the local (Laurel parameters are immutable).
- **error output declaration** — every procedure signature includes
  `maybe_except : Error` so that `try/except` handlers have a
  consistent output to bind.

---

## What Translation Does Not Do

Explicitly: no cast insertion, no literal wrapping, no effect
determination, no coercion. Concretely, these are all jobs for
elaboration (see `ELABORATION.md`):

- Wrapping an `int` into `Any` at a call boundary.
- Narrowing an `Any` back to `bool` for a condition.
- Routing heap state through procedure signatures.
- Binding an effectful call's result at statement level (the
  `effectfulCall` construct).
- Classifying a procedure by grade.

The Laurel output is therefore "surface-typed": the names line up,
the types match at the surface, but effect-related information and
coercions are absent. The only "correctness" Translation guarantees
is the one captured by the Illegal-States-Unrepresentable principle
in `ARCHITECTURE.md`: a `StaticCall f …` is never emitted without `f
∈ Γ` as a function, and arguments are matched against the signature
at construction time.

---

## Rule → Implementation Mapping

The fold is implemented in `Strata/Languages/Python/Translation.lean`
(all entries below are in that file).

### Expressions

| Python construct                     | Lean function                                                                                     |
|--------------------------------------|---------------------------------------------------------------------------------------------------|
| Literals, identifiers, binop         | `translateExpr` leaf cases                                                                        |
| `f(…)` with `f ∈ Γ`                  | `translateCall` → `resolveKwargs` + StaticCall                                                    |
| `f(…)` with `f ∉ Γ`                  | `translateCall` no-sig branch → `.Hole`                                                           |
| `recv.m(…)`                          | `resolveMethodName` + `translateCall`                                                             |
| `recv.f`                             | `translateExpr` (Attribute in expression position)                                                |
| f-strings                            | `translateExpr` (JoinedStr case)                                                                  |
| list / dict literals                 | `translateExpr` (List / Dict cases)                                                               |
| subscript `x[i]`                     | `translateExpr` (Subscript case)                                                                  |
| slice `x[a:b]`                       | `translateExpr` + `from_Slice` constructor                                                        |

### Statements

| Python construct                     | Lean function                                                                                     |
|--------------------------------------|---------------------------------------------------------------------------------------------------|
| `x = p`                              | `translateAssignSingle`                                                                           |
| `x += p`                             | `translateStmt` (AugAssign case)                                                                  |
| `a, b = rhs`                         | `unpackTargets`                                                                                   |
| `x[i] = v`                           | `translateAssignSingle` (Subscript target)                                                        |
| `return p`                           | `translateStmt` (Return case)                                                                     |
| `if` / `while`                       | `translateStmt` (If / While cases)                                                                |
| `for`                                | `translateStmt` (For case) + `pushLoopLabel`                                                      |
| `break` / `continue`                 | `currentBreakLabel` / `currentContinueLabel`                                                      |
| `with`                               | `translateStmt` (With case)                                                                       |
| `try / except`                       | `translateTryExcept`                                                                              |
| `assert`                             | `translateStmt` (Assert case)                                                                     |
| `v = Foo(…)` (class callee)          | `translateCall` (class-callee branch)                                                             |

### Declarations

| Python construct                     | Lean function                                                                                     |
|--------------------------------------|---------------------------------------------------------------------------------------------------|
| `def f(...) → R: body`               | `translateFunction` + `emitScopeDeclarations` + `emitMutableParamCopies`                          |
| `class C: …`                         | `translateClass`                                                                                  |
| module (top-level `stmts`)           | `translateModule` + `collectNestedDefs`                                                           |
