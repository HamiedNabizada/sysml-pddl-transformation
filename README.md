# SysML to PDDL transformation

Generates a PDDL domain and a problem instance from an annotated SysML model. The
transformation runs as a report template in MSoSA and generates only what the model
contains. Missing information yields a note in the generated file, an unsupported construct a
marker.

Requires the profile from the [`pddl-sysml-profile`](https://github.com/HamiedNabizada/pddl-sysml-profile) repository. Built and tested with Magic Systems of Systems Architect (MSoSA) 2024x; the templates run in its Report Wizard (Apache Velocity 2.3).

## Contents

    templates/    The two Velocity templates, one for the domain and one for the problem
    tools/        A check that the generated domain and problem trace back to the model

## Usage

Apply both templates to an annotated model through *Tools → Report Wizard*. `VTL_Domain.vtl`
produces the domain, `VTL_Problem.vtl` the problem instance. The report scope decides which
elements are included. Start both templates at the model root or at another element that contains
the domain and the problem package. The domain template reads the goal of the problem for the
requirements. The problem template needs the predicates to derive facts from object slots.

The [`mps500-planning-example`](https://github.com/HamiedNabizada/mps500-planning-example) repository holds generated domains and problems for 22
models.

## Two ways to describe an action

The domain template reads preconditions and effects in two ways. **Mode B** evaluates the
tags (tagged values) `precondition` and `effect` and renders the formula stereotypes attached to
them. **Mode A** derives both from the pins of the action: an input pin typed with a
`«PDDL_Predicate»` becomes a precondition, an output pin becomes an effect.

The template chooses per action. If at least one of the two tags is set, Mode B
applies to the whole action, otherwise Mode A. If only one of the two is set, the template writes a
note into the generated file.

## Negation

Whatever appears in the precondition and no longer in the effect is deleted, unless it is
marked as preserved, on the pin or on the object flow leading to it. Predicates such as a fixed
adjacency between two stations therefore survive, while the location of a workpiece changes.

The comparison is made on whole atoms, the predicate together with its arguments. Without further
information the template binds the parameters of a pin's predicate to the action parameters by name
or type. A predicate-typed pin can instead name the arguments of its atom in the tag `arguments` of
`«PDDL_PinAnnotation»`, as the names of parameter pins of the same action (`?c` for the pin `c`; an
output pin `cOut` counts as `c`). A move then needs no formula: `(on ?c ?from)` on the input pin and
`(on ?c ?to)` on the output pin are different atoms, so the effect deletes the old position. If the
same predicate is on an input and an output pin and neither carries `arguments`, the two atoms cannot
be told apart, and the generated file carries a warning that suggests `arguments` or Mode B.

## Constants

Instances with `«PDDL_Constant»` become domain constants in `(:constants …)`, named by the tag
`constantName` and typed by `typeRef`. In the problem they count as arguments of init and goal
facts like objects do, but they are not declared again under `:objects`.

## Initial and goal facts

Each `«PDDL_InitState»` or `«PDDL_GoalState»` dependency gives one fact. Its arguments are the clients,
followed by the entries of the tag `additionalArgs`. The tag covers an object that fills two argument
positions, which a second client cannot express.

A goal that facts cannot express, for example a disjunction or a quantifier, goes into the tag `goal`
of the problem as a formula, built like the formulas of a Mode B action. Its atoms name objects and
constants directly, and variables of a quantifier with `?`. The problem template writes it after the
goal facts, in the same `(:goal (and …))`.

## Numbers

Both modes support functions. In Mode B, `«PDDL_Comparison»` and the five numeric effects take numeric
terms: `«PDDL_FunctionAtom»`, `«PDDL_Literal»` and `«PDDL_ArithmeticExpression»` (+, -, *, /, arbitrarily nested). The target
of a numeric effect takes its arguments from the tag `targetArguments`, e.g. `(increase (station-load ?ct) 1.0)`.

In Mode A, a pin typed with a `«PDDL_Function»` carries a numeric condition or effect through `«PDDL_PinAnnotation»`:
`comparison` on an input pin gives `(< (station-load ?ct) 3.0)` in the precondition, `numericEffect` on an output pin
gives `(increase (station-load ?ct) 1.0)` in the effect. The right-hand side is `numericValue` or `numericOperand`. The
function's arguments are bound to the action parameters like a predicate's. Object flows carry no numbers.

In both modes, the tag `cost` on an action adds `(increase (total-cost) 3)` to its effect, here for a cost of 3. This
needs a function `total-cost` without parameters. If the action already changes `total-cost` itself, that effect counts
and the generated file carries a warning.

## Requirements

The domain template writes the entries of the tag `requirements` first and keeps them. It always adds `:strips` and
`:typing` and then what the model uses, following the requirement flags of the PDDL 2.1 grammar:

| Requirement | Written when |
|---|---|
| `:negative-preconditions` | `not` before a single predicate in a precondition, a `when` condition or the goal, or a negated input pin (Mode A) or goal fact |
| `:disjunctive-preconditions` | `or`, `imply`, or `not` before a formula that is not a single predicate |
| `:existential-preconditions` | `exists` |
| `:universal-preconditions` | `forall` in a precondition, a `when` condition or the goal |
| `:conditional-effects` | `when`, or `forall` in an effect |
| `:action-costs` | a function `total-cost` without parameters that only grows by `increase`, by a number of at least 0 or by the value of another function, while no condition compares a function value, no other function changes and the metric minimizes `total-cost` |
| `:numeric-fluents` | any other use of functions |

An entry that the tag already names or covers is not repeated. `:quantified-preconditions` covers the existential
and universal ones, `:numeric-fluents` covers `:action-costs`. A call is a call behavior action with `«PDDL_Action»`.
Several calls with the same action name give one action, and the template reads its first call, as it does when it
writes the actions.

For every entry of the tag that no construct of the domain or of the goal needs, the template writes a warning
comment below the requirements line, because a planner that does not support it may reject the domain.
`:action-costs` counts as needed when the functions carry only action costs, `:numeric-fluents` when they carry more.
Eight literals of the profile enumeration `PDDLRequirement` (`:equality`,
`:durative-actions`, `:duration-inequalities`, `:continuous-effects`, `:derived-predicates`, `:timed-initial-literals`,
`:preferences`, `:constraints`) belong to constructs the templates do not generate, so they always get this warning.

## Known limitations

- Durative actions can be specified but are not generated.
- Each template expects one package with `«PDDL_Domain»` or `«PDDL_Problem»` below the element where the
  report starts. With several, it writes an error line naming them instead of a file that mixes them.
- Init facts derived from object slots need exactly one binary predicate whose parameter types match
  owner and value. If none or several match, or if no predicate is within the report scope, the problem
  template writes a warning into the generated file instead of a fact.
- A goal whose client is a type becomes one goal per object of that type or of one of its subtypes
  (following the generalizations). With `isNegated` each of these goals is negated. This needs a
  predicate with exactly one parameter. Functions or other arities give a warning in the generated
  file instead of a goal.
- A function pin without `comparison` or `numericEffect`, or without exactly one right-hand side, is not
  transformed; the domain template writes a warning for it. In a Mode B action, numeric pin annotations are
  ignored, with a warning.
- If the number of `targetArguments` differs from the arity of the target function, the domain template writes a
  warning and renders the target as modeled.
- The domain template writes general numeric fluents. Fast Downward and the planners built on it
  reject them.

## License

Copyright (c) 2026 Hamied Nabizada. Licensed under the MIT License, see [LICENSE](LICENSE).
