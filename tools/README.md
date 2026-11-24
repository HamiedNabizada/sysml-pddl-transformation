# Traceability check

`traceability_check.py` checks a generated domain and problem against the annotated model they come
from. It works in both directions. Every annotated model element has to appear in the generated files
(source coverage), and every element of the generated files has to go back to a model element (target
justification). It needs Python 3.8 or later and no further packages.

    python traceability_check.py --model MPS500_B.mdzip \
        --domain MPS500_B_Domain.pddl --problem MPS500_B_Problem.pddl --self-test

The check reads the expected content from the model alone, from the XMI inside the `.mdzip`, never from the
templates. It implements the transformation rules a second time. It therefore finds a template that deviates from
the rules, but not an error in the model or in the rules themselves.

With `--self-test` the check injects three faults into the generated content before comparing again: it
removes an action, adds an init fact and swaps the arguments of a precondition. All three have to be
reported, otherwise the exit code is 2. Without findings the exit code is 0, with findings 1. The report
goes to `TRACE_<domain>.md` and `.json` in `--out-dir`.

## Results for the example models

For the 22 models of [`mps500-planning-example`](https://github.com/HamiedNabizada/mps500-planning-example), the self-test finds all three faults in every model.

| Models | Findings |
|---|---|
| `B`, `I1` to `I12`, `T1` to `T3`, `P1` to `P3` | none |
| `V1`, `V2` | one each: the unused predicate `stored` (see below) |
| `V3` | seven: the unused predicate `stored` as in `V1` and `V2`, and two for each of its three injected errors, which the template marks as `UNKNOWN-…` in the generated domain |

## Unused annotated elements

The templates write every annotated predicate, function and type. The check expects only those that an
action, a fact or a goal uses. An annotated element that nothing uses is therefore reported as a finding, with the message `declared in the model but not used`,
as `stored` is in `V1` to `V3`.

## License

Copyright (c) 2026 Hamied Nabizada. Licensed under the MIT License, see [LICENSE](../LICENSE).
