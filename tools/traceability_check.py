#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Checks that generated PDDL traces back to the annotated SysML model.

Two directions are checked:

  source coverage        every annotated model element appears in the generated domain or problem
  target justification   every element of the generated domain and problem goes back to a model element

The expected content is read from the model alone (the XMI inside the .mdzip), never from the
templates. It is a second implementation of the transformation rules, written independently of the
templates, but it shares the rules with them: it checks structural origin, not whether the model is
right.

With --self-test the check injects three faults into the generated content (an action removed, an
init fact added, the arguments of a precondition swapped) and must report all three.

    python traceability_check.py --model MODEL.mdzip --domain DOMAIN.pddl --problem PROBLEM.pddl \
        [--self-test] [--out-dir DIR] [--label NAME]

The names of domain and problem are taken from the generated files. The report goes to
<out-dir>/TRACE_<label>.md and .json. Exit code 0: no findings, 1: findings, 2: self-test failed.

Annotated predicates, functions and types that no action, fact or goal uses are reported as findings.
The templates write every annotated element, but the check expects only the used ones.
"""
import argparse, copy, hashlib, json, os, re, sys, zipfile
import xml.etree.ElementTree as ET
from collections import defaultdict


def local(tag):
    return tag.split('}')[-1]


def attrs_local(elem):
    return {local(k): v for k, v in elem.attrib.items()}


# ------------------------------------------------------------------------------------- model side
class Model:
    """Indexes the model XMI: elements by id, parents, and the PDDL stereotype applications."""

    def __init__(self, xml_bytes):
        self.root = ET.fromstring(xml_bytes)
        self.byid, self.parent = {}, {}
        self.stereo = defaultdict(list)          # base element id -> [(stereotype, tags)]
        for elem in self.root.iter():
            a = attrs_local(elem)
            if 'id' in a:
                self.byid[a['id']] = elem
            for child in elem:
                self.parent[child] = elem
        for elem in self.root.iter():
            name = local(elem.tag)
            if not name.startswith('PDDL_'):
                continue
            a = attrs_local(elem)
            base = next((v for k, v in a.items() if k.startswith('base_')), None)
            if base is None:
                continue
            tags = {k: v for k, v in a.items() if not k.startswith('base_') and k != 'id'}
            for child in elem:                   # multi-valued tags are child elements
                tags.setdefault('_' + local(child.tag), []).append(
                    (child.text or '').strip() or attrs_local(child).get('idref', ''))
            self.stereo[base].append((name, tags))

    def stereos_of(self, eid):
        return self.stereo.get(eid, [])

    def id_of(self, elem):
        return attrs_local(elem).get('id')

    def under(self, elem, pkg_id):
        cur = elem
        while cur is not None:
            if self.id_of(cur) == pkg_id:
                return True
            cur = self.parent.get(cur)
        return False

    def name(self, eid):
        e = self.byid.get(eid)
        return attrs_local(e).get('name') if e is not None else None

    def refs(self, elem, childname):
        out = []
        for child in elem:
            if local(child.tag) == childname:
                a = attrs_local(child)
                out.append(a.get('idref') or a.get('href', '').lstrip('#'))
        return out


NUM_EFFECTS = ('increase', 'increase-nested', 'decrease', 'assign', 'scale-up', 'scale-down')


def strip_num(v):
    """'21.0' -> '21', other values unchanged."""
    try:
        f = float(v)
        return str(int(f)) if f == int(f) else str(f)
    except (ValueError, TypeError):
        return v


CMP_PDDL = {'greaterThan': '>', 'lessThan': '<', 'greaterOrEqual': '>=', 'lessOrEqual': '<=',
            'equal': '=', 'notEqual': '!='}
NUM_EFFECT = {'PDDL_Assign': 'assign', 'PDDL_Decrease': 'decrease',
              'PDDL_ScaleUp': 'scale-up', 'PDDL_ScaleDown': 'scale-down'}
NUM_VALUE_TAG = {'PDDL_ScaleUp': 'factor', 'PDDL_ScaleDown': 'divisor'}
GEN_NESTED = {'or', 'imply', 'forall', 'exists', 'when', 'assign', 'decrease', 'scale-up',
              'scale-down', '>', '<', '>=', '<=', '=', '!='}


def merged_requirements(tag, derived):
    """The entries of the tag, then the base and the derived requirements unless the tag names them or covers them
    by :quantified-preconditions (or, for :action-costs, by :numeric-fluents), as the domain template does."""
    r = list(tag)
    quant = 'quantified-preconditions' in r
    covered = {'strips': False, 'typing': False, 'negative-preconditions': False, 'disjunctive-preconditions': False,
               'existential-preconditions': quant, 'universal-preconditions': quant, 'conditional-effects': False,
               'action-costs': 'numeric-fluents' in r, 'numeric-fluents': False}
    for x in ['strips', 'typing'] + [y for y in derived if y in covered]:
        if x not in r and not covered.get(x, False):
            r.append(x)
    return [':' + x for x in r]


def derived_requirements(m):
    """Requirements derived from the constructs used, as the domain template does.
    Conditions ('pre'): preconditions, the condition of a when or imply, the goal formula of a problem; effects ('eff').
    or/imply, and not around a non-atom in a condition -> disjunctive-preconditions; exists -> existential-preconditions;
    forall in a condition -> universal-preconditions, in an effect -> conditional-effects; when -> conditional-effects."""
    flags = set()
    seen = set()

    def scan(eid, where):
        if not eid or (eid, where) in seen:
            return
        seen.add((eid, where))
        for s, t in m.stereos_of(eid):
            if s in ('PDDL_Or', 'PDDL_Imply'):
                flags.add('disjunctive-preconditions')
            if s == 'PDDL_Exists':
                flags.add('existential-preconditions')
            if s == 'PDDL_Forall':
                flags.add('conditional-effects' if where == 'eff' else 'universal-preconditions')
            if s == 'PDDL_ConditionalEffect':
                flags.add('conditional-effects')
            if s == 'PDDL_Not' and where != 'eff':
                op = _single(t, 'operand')
                if op and not any(s2 == 'PDDL_PredicateAtom' for s2, _ in m.stereos_of(op)):
                    flags.add('disjunctive-preconditions')
                elif op:
                    flags.add('negative-preconditions')
            for k in _multi(t, 'condition'):
                scan(k, 'pre')
            for name in ('operands', 'operand', 'scope', 'consequence', 'effect'):
                for k in _multi(t, name):
                    scan(k, where)

    for base, apps in m.stereo.items():
        for s, t in apps:
            if s == 'PDDL_Action':
                scan(_single(t, 'precondition'), 'pre')
                scan(_single(t, 'effect'), 'eff')
            if s == 'PDDL_Problem':
                scan(_single(t, 'goal'), 'pre')
    return [x for x in ('negative-preconditions', 'disjunctive-preconditions', 'existential-preconditions',
                        'universal-preconditions', 'conditional-effects') if x in flags]


def nonnegative(v):
    """The amount of an increase of total-cost must be a number >= 0."""
    try:
        return float(strip_num(v)) >= 0
    except (TypeError, ValueError):
        return False


def ac_value(m, wid, tc_id, ac):
    """Amount as a formula: literal >= 0 or function atom of a function other than total-cost."""
    for s, t in (m.stereos_of(wid) if wid else []):
        if s == 'PDDL_Literal':
            ac[0] = ac[0] and nonnegative(t.get('value'))
            return
        if s == 'PDDL_FunctionAtom':
            ac[0] = ac[0] and t.get('function') != tc_id
            return
    ac[0] = False


def ac_scan(m, eid, tc_id, ac, seen=None):
    """Checks a formula tree for action costs, as the domain template does: no comparison, numeric effects only
    increase on total-cost. Children as when deriving the requirements."""
    if not eid:
        return
    seen = set() if seen is None else seen
    if eid in seen:
        return
    seen.add(eid)
    for s, t in m.stereos_of(eid):
        if s == 'PDDL_Comparison':
            ac[0] = False
        if s == 'PDDL_Increase' or s in NUM_EFFECT:
            if s != 'PDDL_Increase' or t.get('target') != tc_id:
                ac[0] = False
            else:
                ac_value(m, _single(t, 'value'), tc_id, ac)
        for name in ('condition', 'operands', 'operand', 'scope', 'consequence', 'effect'):
            for k in _multi(t, name):
                ac_scan(m, k, tc_id, ac, seen)


def _multi(t, name):
    """Multi-valued tag, serialized either as child elements or as a space-separated attribute."""
    v = t.get('_' + name)
    if v:
        return [x for x in v if x]
    v = t.get(name)
    return v.split() if v else []


def _single(t, name):
    v = t.get(name)
    if v:
        return v
    lst = t.get('_' + name) or []
    return lst[0] if lst else None


AR_OP = {'plus': '+', 'minus': '-', 'times': '*', 'divide': '/'}


def num_term(m, eid, funcs, ref_funcs):
    """Numeric term (function atom, literal, arithmetic expression) -> hashable value as in canon()."""
    for s, t in (m.stereos_of(eid) if eid else []):
        if s == 'PDDL_FunctionAtom':
            ref_funcs.add(t['function'])
            return ('atom', (funcs[t['function']]['name'],) + tuple(t.get('_arguments', [])))
        if s == 'PDDL_Literal':
            v = t.get('value')
            return ('lit', strip_num(v) if v is not None else None)
        if s == 'PDDL_ArithmeticExpression':
            op = _single(t, 'operator')
            op = m.name(op) or op
            return ('arith', AR_OP.get(op, op), num_term(m, _single(t, 'left'), funcs, ref_funcs),
                    num_term(m, _single(t, 'right'), funcs, ref_funcs))
    return ('NOT-CHECKABLE', 'numeric term')


def build_expected(m, domain_name, problem_name):
    """Expected content, read from the model. Every entry keeps its rule and its source element."""
    exp = {'warnings': []}
    dom_pkg = prob_pkg = None
    dom_reqs, metric = [], None
    for base, apps in m.stereo.items():
        for s, t in apps:
            if s == 'PDDL_Domain' and t.get('domainName') == domain_name:
                dom_pkg = base
                dom_reqs = t.get('_requirements', [])
            if s == 'PDDL_Problem' and t.get('problemName') == problem_name:
                prob_pkg = base
                if t.get('metricDirection'):
                    metric = (t['metricDirection'], t.get('metricExpression'))
    # Several problems in one model: collect model-wide, but skip the subtrees of the other problems.
    other_problems = [b for b, apps in m.stereo.items() for s, _ in apps if s == 'PDDL_Problem' and b != prob_pkg]

    def foreign(e):
        return bool(other_problems) and e is not None and any(m.under(e, fp) for fp in other_problems)

    if not dom_pkg or not prob_pkg:
        sys.exit('ERROR: domain or problem package not found (%r / %r)' % (domain_name, problem_name))
    exp['domain_name'], exp['problem_name'] = domain_name, problem_name
    exp['requirements'] = [':' + r for r in dom_reqs]
    exp['metric'] = metric

    type_name = {}
    for base, apps in m.stereo.items():
        for s, t in apps:
            if s == 'PDDL_Type' and t.get('typeName'):
                type_name[base] = t['typeName']
            elif s == 'PDDL_Type' and m.name(base):
                type_name[base] = m.name(base).lower()      # without typeName the element name counts

    def sig_params(sig_id):
        e = m.byid.get(sig_id)
        if e is None:
            return []
        return [(attrs_local(c).get('name'), type_name.get(attrs_local(c).get('type')))
                for c in e if local(c.tag) == 'ownedAttribute']

    # Predicates and functions are indexed model-wide; which of them belong to the domain is decided by
    # the references from actions, init, goal and slots, not by package containment.
    preds, funcs = {}, {}
    for base, apps in m.stereo.items():
        e = m.byid.get(base)
        if e is None:
            continue
        for s, t in apps:
            if s == 'PDDL_Predicate':
                preds[base] = {'name': t.get('predicateName') or attrs_local(e).get('name'),
                               'params': sig_params(base), 'src': base}
            if s == 'PDDL_Function':
                funcs[base] = {'name': t.get('functionName') or attrs_local(e).get('name'),
                               'params': sig_params(base), 'src': base}
    referenced_preds, referenced_funcs = set(), set()
    # The requirements are assembled at the end (negation from Mode A and goal facts, action costs). Here only the
    # flags are collected.
    tc_id = next((k for k, v in funcs.items() if str(v['name']).lower() == 'total-cost' and not v['params']), None)
    ac = [tc_id is not None]                        # action costs possible until something does not fit
    goal_negated = [False]

    supertype = {}
    for cid, tn in type_name.items():
        for child in m.byid.get(cid, []):
            if local(child.tag) == 'generalization':
                g = type_name.get(attrs_local(child).get('general'))
                if g:
                    supertype.setdefault(tn, g)

    def is_subtype(tn, target):                    # follows the first generalization up to the root, stops at a cycle
        seen = set()
        while tn is not None and tn not in seen:
            if tn == target:
                return True
            seen.add(tn)
            tn = supertype.get(tn)
        return False

    # Actions: call behavior actions with <<PDDL_Action>>, model-wide. Calls with the same actionName give
    # one schema, the first one wins as in the template; differing calls are reported as a warning.
    actions = {}
    # Object flows with <<PDDL_FlowAnnotation>>, by pin end: (pin id, 'in') for the target of a flow,
    # (pin id, 'out') for its source.
    flow_ann = {}
    for fe in m.root.iter():
        if local(fe.tag) != 'edge':
            continue
        fa = attrs_local(fe)
        tags = next((t for s, t in m.stereos_of(fa.get('id')) if s == 'PDDL_FlowAnnotation'), None)
        if tags is None:
            continue
        src = fa.get('source') or (m.refs(fe, 'source') or [None])[0]
        tgt = fa.get('target') or (m.refs(fe, 'target') or [None])[0]
        if tgt:
            flow_ann.setdefault((tgt, 'in'), tags)
        if src:
            flow_ann.setdefault((src, 'out'), tags)
    for base, apps in m.stereo.items():
        e = m.byid.get(base)
        if e is None:
            continue
        act = next((t for s, t in apps if s == 'PDDL_Action'), None)
        if act is None:
            continue
        # As the template: actionName, otherwise the element name; without both no action (the template warns).
        nm = act.get('actionName') or attrs_local(e).get('name')
        if not nm:
            continue
        in_pins, out_pins = [], []
        for child in e:
            lt = local(child.tag)
            if lt in ('argument', 'result'):
                a = attrs_local(child)
                pin = {'name': a.get('name'), 'type': a.get('type'), 'id': a.get('id')}
                (in_pins if lt == 'argument' else out_pins).append(pin)
        obj_pins = [p for p in in_pins if p['type'] in type_name]
        for p in out_pins:          # parameter pins on the output side: lower case, without the suffix 'Out'
            if p['type'] in type_name and p['name']:
                n = p['name'][:-3] if p['name'].endswith('Out') else p['name']
                if n.lower() not in [q['name'].lower() for q in obj_pins]:
                    obj_pins.append(dict(p, name=n))
        pred_in = [p for p in in_pins if p['type'] in preds]
        pred_out = [p for p in out_pins if p['type'] in preds]
        params = [('?' + p['name'].lower(), type_name[p['type']]) for p in obj_pins]

        def bind(sig_id):
            """Name match first, then type match including subtypes at any depth."""
            args = []
            sig = preds.get(sig_id) or funcs[sig_id]
            for anm, atyp in sig['params']:
                hit = next((p for p in obj_pins if p['name'] == anm), None)
                if hit is None:
                    cands = [p for p in obj_pins if is_subtype(type_name.get(p['type']), atyp)]
                    if len(cands) != 1:
                        exp['warnings'].append('action %s: ambiguous or missing binding for %s.%s'
                                               % (nm, sig['name'], anm))
                    hit = cands[0] if cands else None
                args.append('?' + hit['name'].lower() if hit else '?' + anm.lower())
            return tuple(args)

        first = nm not in actions                   # as in the template, the first call per action name counts
        if act.get('precondition') or act.get('effect'):
            mode = 'B'
            if first:
                ac_scan(m, act.get('precondition'), tc_id, ac)
                ac_scan(m, act.get('effect'), tc_id, ac)
            pre = resolve_formula(m, act.get('precondition'), preds, funcs, referenced_preds, referenced_funcs, type_name)
            eff = resolve_formula(m, act.get('effect'), preds, funcs, referenced_preds, referenced_funcs, type_name)
            if act.get('parameters'):
                params = parse_param_string(act['parameters'])
        else:
            mode = 'A'
            pre, eff = set(), set()
            for p in pred_in + pred_out:
                referenced_preds.add(p['type'])

            def pin_ann(p):
                if any(s == 'PDDL_PinAnnotation' for s, _ in m.stereos_of(p['id'])):
                    return {k: v for s, t in m.stereos_of(p['id']) if s == 'PDDL_PinAnnotation' for k, v in t.items()}
                # without an annotation on the pin, the one on the object flow applies (the pin takes precedence)
                return dict(flow_ann.get((p['id'], 'in' if p in in_pins else 'out'), {}))

            def pin_atom(p, ann):
                args = ann.get('_arguments') or []
                if args:
                    return (preds[p['type']]['name'],) + tuple('?' + a.strip().lstrip('?').lower() for a in args)
                return (preds[p['type']]['name'],) + bind(p['type'])

            out_pos = set()
            for p in pred_out:
                ann = pin_ann(p)
                atom = pin_atom(p, ann)
                if ann.get('isNegated') == 'true':
                    eff.add(('not', atom))
                else:
                    eff.add(('atom', atom))
                    out_pos.add(atom)
            for p in pred_in:
                ann = pin_ann(p)
                atom = pin_atom(p, ann)
                if ann.get('isNegated') == 'true':
                    pre.add(('not', atom))
                else:
                    pre.add(('atom', atom))
                    if ann.get('isPreserved') != 'true' and atom not in out_pos:
                        eff.add(('not', atom))

            def rhs(ann, flat):
                if ann.get('numericValue') is not None:
                    return ('lit', strip_num(ann['numericValue']))
                oid = ann.get('numericOperand')
                for s2, t2 in (m.stereos_of(oid) if oid else []):
                    if s2 == 'PDDL_FunctionAtom':
                        referenced_funcs.add(t2['function'])
                        f = (funcs[t2['function']]['name'],) + tuple(t2.get('_arguments', []))
                        return f if flat else ('atom', f)
                    if s2 == 'PDDL_Literal':
                        return ('lit', strip_num(t2.get('value')))
                    if s2 == 'PDDL_ArithmeticExpression':
                        return num_term(m, oid, funcs, referenced_funcs)
                return ('NOT-CHECKABLE', 'numericOperand')

            for p in in_pins + out_pins:
                if p['type'] not in funcs:
                    continue
                referenced_funcs.add(p['type'])
                ann = pin_ann(p)
                target = (funcs[p['type']]['name'],) + bind(p['type'])
                if p in in_pins:
                    op = m.name(ann.get('comparison')) or ann.get('comparison')
                    if first and ann.get('comparison'):
                        ac[0] = False                    # comparison of a function value
                    pre.add(('cmp', CMP_PDDL.get(op, op), ('atom', target), rhs(ann, False)))
                else:
                    kind = m.name(ann.get('numericEffect')) or ann.get('numericEffect')
                    if first and ann.get('numericEffect'):   # only increase on total-cost, amount >= 0 or a function
                        if kind != 'increase' or p['type'] != tc_id:
                            ac[0] = False
                        elif ann.get('numericOperand'):
                            ac_value(m, ann.get('numericOperand'), tc_id, ac)
                        elif ann.get('numericValue') is not None:
                            ac[0] = ac[0] and nonnegative(ann.get('numericValue'))
                    if kind == 'increase':
                        eff.add(('increase', target, rhs(ann, True)))
                    else:
                        kind = {'scaleUp': 'scale-up', 'scaleDown': 'scale-down'}.get(kind, kind)
                        eff.add((kind, target, rhs(ann, False)))
        # The tag 'cost' gives (increase (total-cost) cost), unless the action changes total-cost itself (then its
        # own effect counts and the template warns) or the model has no function total-cost.
        cost = act.get('cost')
        if cost is not None and tc_id is not None:
            tc_name = funcs[tc_id]['name']
            if not any(isinstance(x, tuple) and len(x) >= 2 and x[0] in NUM_EFFECTS and x[1] == (tc_name,)
                       for x in eff):
                eff.add(('increase', (tc_name,), ('lit', strip_num(cost))))
                if first:
                    ac[0] = ac[0] and nonnegative(cost)
        entry = {'name': nm, 'mode': mode, 'params': params, 'pre': pre, 'eff': eff, 'src': base,
                 'srcname': attrs_local(e).get('name')}
        if nm in actions:
            prev = actions[nm]
            prev.setdefault('srcnames', [prev['srcname']]).append(entry['srcname'])
            if (prev['params'], prev['pre'], prev['eff']) != (entry['params'], entry['pre'], entry['eff']):
                exp['warnings'].append('action %s: several calls with different definitions (%r vs. %r), '
                                       'the first one wins as in the template' % (nm, prev['srcname'], entry['srcname']))
        else:
            actions[nm] = entry
    exp['actions'] = actions

    used_types, objects = set(), {}
    for base, apps in m.stereo.items():
        e = m.byid.get(base)
        if e is None or foreign(e):
            continue
        for s, t in apps:
            if s == 'PDDL_Object':
                cls = m.refs(e, 'classifier')
                tn = type_name.get(cls[0]) if cls else None
                nm = t.get('objectName') or attrs_local(e).get('name')
                if tn:
                    objects[base] = {'name': nm, 'type': tn, 'src': base}
                    used_types.add(tn)
    exp['objects'] = objects
    obj_name = {k: v['name'] for k, v in objects.items()}

    # Constants: declared in (:constants ...) of the domain, arguments of init and goal facts and slots like
    # objects. Type from typeRef, otherwise from the classifier.
    constants = {}
    for base, apps in m.stereo.items():
        e = m.byid.get(base)
        if e is None:
            continue
        for s, t in apps:
            if s == 'PDDL_Constant':
                cls = m.refs(e, 'classifier')
                ctype = type_name.get(cls[0]) if cls else None
                tn = type_name.get(_single(t, 'typeRef')) or ctype
                constants[base] = {'name': t.get('constantName') or attrs_local(e).get('name'),
                                   'type': tn, 'ctype': ctype, 'src': base}
                if tn:
                    used_types.add(tn)
    exp['constants'] = constants
    obj_name.update({k: v['name'] for k, v in constants.items()})
    arguments = set(objects) | set(constants)

    init, goal, init_src, goal_src = set(), set(), {}, {}
    for base, apps in m.stereo.items():
        e = m.byid.get(base)
        if e is None or foreign(e):
            continue
        for s, t in apps:
            if s not in ('PDDL_InitState', 'PDDL_GoalState'):
                continue
            sups, clients_raw = m.refs(e, 'supplier'), m.refs(e, 'client')
            # Only object and constant clients are arguments; a nullary function carries the problem package
            # as a formal client because UML requires at least one client.
            clients = [c for c in clients_raw if c in arguments]
            clients += [c for c in _multi(t, 'additionalArgs') if c in arguments]
            if not sups:
                continue
            sup = sups[0]
            if s == 'PDDL_InitState':
                if sup in funcs or t.get('value') is not None:
                    referenced_funcs.add(sup)
                    if sup in funcs and t.get('value') is None:
                        continue                   # without 'value' no fact; the template warns
                    fact = ('=', (funcs[sup]['name'],) + tuple(obj_name.get(c, m.name(c)) for c in clients),
                            strip_num(t.get('value', '0')))
                else:
                    referenced_preds.add(sup)
                    # isNegated on the initial state gives (not atom)
                    fact = ('not' if t.get('isNegated') == 'true' else 'atom',
                            (preds[sup]['name'],) + tuple(obj_name.get(c, m.name(c)) for c in clients))
                init.add(fact)
                init_src[fact] = base
            else:
                if sup in funcs:                    # function value as goal: (= (f args) value)
                    referenced_funcs.add(sup)
                    ac[0] = False                   # a function goal is a comparison
                    fact = ('cmp', '=', ('atom', (funcs[sup]['name'],) +
                                         tuple(obj_name.get(c, m.name(c)) for c in clients)),
                            ('lit', strip_num(t.get('value', '0'))))
                    goal.add(fact)
                    goal_src[fact] = base
                    continue
                referenced_preds.add(sup)
                neg = t.get('isNegated') == 'true'
                if neg:
                    goal_negated[0] = True          # a negated goal fact needs :negative-preconditions

                def goal_fact(atom):
                    return ('not', atom) if neg else ('atom', atom)
                for c in clients_raw:
                    if c in type_name:              # goal over a type: one goal per object of the type
                        for ov in objects.values():
                            if is_subtype(ov['type'], type_name[c]):
                                fact = goal_fact((preds[sup]['name'], ov['name']))
                                goal.add(fact)
                                goal_src[fact] = base
                        for kv in constants.values():   # constants count by their classifier
                            if kv['ctype'] and is_subtype(kv['ctype'], type_name[c]):
                                fact = goal_fact((preds[sup]['name'], kv['name']))
                                goal.add(fact)
                                goal_src[fact] = base
                    else:
                        fact = goal_fact((preds[sup]['name'],) + tuple(obj_name.get(x, m.name(x)) for x in clients))
                        goal.add(fact)
                        goal_src[fact] = base
                        break

    # Init facts from slots: a slot whose value is an object gives a binary predicate, chosen by the type
    # signature among the referenced binary predicates.
    bin_preds = defaultdict(list)
    for k in referenced_preds:
        p = preds.get(k)
        if p and len(p['params']) == 2:
            bin_preds[(p['params'][0][1], p['params'][1][1])].append(k)
    every = dict(objects)
    every.update(constants)
    for oid, ov in every.items():
        for child in m.byid[oid]:
            if local(child.tag) != 'slot':
                continue
            for val in child:
                if local(val.tag) != 'value':
                    continue
                inst = attrs_local(val).get('instance')
                if inst and inst in every:
                    key = (ov['type'], every[inst]['type'])
                    cands = bin_preds.get(key, [])
                    if len(cands) == 1:
                        fact = ('atom', (preds[cands[0]]['name'], ov['name'], every[inst]['name']))
                        init.add(fact)
                        init_src[fact] = oid
                    elif len(cands) > 1:
                        exp['warnings'].append('slot %s: ambiguous signature %s' % (ov['name'], key))
    # Goal formula in the tag 'goal' of the problem, read like the formulas of the actions (the problem template renders
    # it with the same macros, after the goal facts)
    for s, t in m.stereo.get(prob_pkg, []):
        if s == 'PDDL_Problem' and t.get('goal'):
            ac_scan(m, t['goal'], tc_id, ac)
            for lit in resolve_formula(m, t['goal'], preds, funcs, referenced_preds, referenced_funcs, type_name):
                goal.add(lit)
                goal_src[lit] = t['goal']
    exp['init'], exp['init_src'], exp['goal'], exp['goal_src'] = init, init_src, goal, goal_src
    # Requirements as the domain template sets them: the tag, :strips :typing, the derived ones; :negative-preconditions
    # only when a condition, a Mode A input pin or a goal fact negates a predicate; for functions :action-costs when
    # they carry only action costs, otherwise :numeric-fluents
    derived = derived_requirements(m)
    negated = 'negative-preconditions' in derived or goal_negated[0] or any(
        a['mode'] == 'A' and any(isinstance(l, tuple) and l and l[0] == 'not' for l in a['pre'])
        for a in actions.values())
    derived = [x for x in derived if x != 'negative-preconditions']
    numeric = []
    if funcs:
        numeric = ['action-costs' if (ac[0] and metric is not None and str(metric[0]).lower() == 'minimize'
                                      and str(metric[1]).strip().lower() == 'total-cost') else 'numeric-fluents']
    if not dom_reqs:
        exp['requirements'] = [':strips', ':typing'] + ([':negative-preconditions'] if negated else []) + \
                              [':' + x for x in derived + numeric]
    else:
        exp['requirements'] = merged_requirements([str(x).lower().lstrip(':') for x in dom_reqs],
                                                  (['negative-preconditions'] if negated else []) + derived + numeric)
    exp['predicates'] = {k: preds[k] for k in referenced_preds if k in preds}
    exp['functions'] = {k: funcs[k] for k in referenced_funcs if k in funcs}
    # Names of all annotated predicates and functions, used or not: a generated declaration of an unused one is
    # reported as unused, not as an element without a model source
    exp['declared'] = {'predicates': {str(p['name']).lower() for p in preds.values()},
                       'functions': {str(f['name']).lower() for f in funcs.values()}}

    for p in list(exp['predicates'].values()) + list(exp['functions'].values()):
        for _, tn in p['params']:
            if tn:
                used_types.add(tn)
    for a in actions.values():
        for _, tn in a['params']:
            if tn and tn != 'object':
                used_types.add(tn)

    def quantifier_types(x):                     # variable types of forall/exists count as used
        if isinstance(x, (tuple, frozenset)):
            if isinstance(x, tuple) and len(x) == 3 and x[0] in ('forall', 'exists') and isinstance(x[1], tuple):
                for _, tq in x[1]:
                    if tq:
                        used_types.add(tq)
            for y in x:
                quantifier_types(y)
    for a in actions.values():
        quantifier_types(tuple(a['pre']))
        quantifier_types(tuple(a['eff']))
    lower = {v.lower(): v for v in type_name.values()}
    for tq in list(used_types):
        if tq not in type_name.values() and tq in lower:
            used_types.add(lower[tq])
    changed = True                              # parent types are written by the template as well
    while changed:
        changed = False
        for cid, tn in type_name.items():
            if tn not in used_types:
                continue
            for child in m.byid[cid]:
                if local(child.tag) == 'generalization':
                    g = type_name.get(attrs_local(child).get('general'))
                    if g and g not in used_types:
                        used_types.add(g)
                        changed = True
    types = {}
    for cid, tn in type_name.items():
        if tn not in used_types:
            continue
        parent = None
        for child in m.byid.get(cid):
            if local(child.tag) == 'generalization':
                gen = attrs_local(child).get('general')
                if type_name.get(gen) in used_types:
                    parent = type_name[gen]
        types[tn] = {'name': tn, 'parent': parent or 'object', 'src': cid}
    exp['types'] = types
    exp['declared']['types'] = {str(tn).lower() for tn in type_name.values()}
    return exp


def canon_gen(node):
    """Generated formula node -> one hashable value; counterpart of canon() on the model side."""
    if not isinstance(node, list):
        return ('lit', strip_num(node))
    if not node:
        return ('EMPTY',)
    h = node[0]
    if h == 'and' and len(node) == 2:       # (and X) is X
        return canon_gen(node[1])
    if h in ('and', 'or'):
        return (h, frozenset(canon_gen(s) for s in node[1:]))
    if h == 'not':
        return ('not', canon_gen(node[1]))
    if h == 'imply':
        return ('imply', canon_gen(node[1]), canon_gen(node[2]))
    if h in ('forall', 'exists'):
        try:
            pairs = tuple((v.lower(), (ty or '').lower()) for v, ty in typed_list(node[1]))
        except (IndexError, AttributeError, TypeError):
            return ('NOT-CHECKABLE', h + '/variables')
        return (h, pairs, canon_gen(node[2]))
    if h == 'when':
        return ('when', canon_gen(node[1]), canon_gen(node[2]))
    if h in ('>', '<', '>=', '<=', '=', '!='):
        return ('cmp', h, canon_gen(node[1]), canon_gen(node[2]))
    if h in ('+', '-', '*', '/') and len(node) == 3:
        return ('arith', h, canon_gen(node[1]), canon_gen(node[2]))
    if h in ('assign', 'decrease', 'scale-up', 'scale-down', 'increase'):
        tgt = tuple(node[1]) if isinstance(node[1], list) else (node[1],)
        return ('increase-nested' if h == 'increase' else h, tgt, canon_gen(node[2]))
    if any(isinstance(x, list) for x in node):
        return ('NOT-CHECKABLE', str(h))
    return ('atom', tuple(node))


def resolve_formula(m, fid, preds, funcs, ref_preds, ref_funcs, type_name=None):
    """Mode B formula tree -> set of normalized literals (conjunctions flattened)."""
    out = set()
    type_name = type_name or {}

    def canon(eid):
        if not eid:
            return ('EMPTY',)
        stereos = m.stereos_of(eid)
        for s, t in stereos:
            if s == 'PDDL_And' and len(_multi(t, 'operands')) == 1:     # (and X) is X, as on the generated side
                return canon(_multi(t, 'operands')[0])
            if s in ('PDDL_And', 'PDDL_Or'):
                return ('and' if s == 'PDDL_And' else 'or', frozenset(canon(o) for o in _multi(t, 'operands')))
            if s == 'PDDL_Not':
                return ('not', canon(_single(t, 'operand')))
            if s == 'PDDL_Imply':
                return ('imply', canon(_single(t, 'condition')), canon(_single(t, 'consequence')))
            if s in ('PDDL_Exists', 'PDDL_Forall'):
                vs = [v.lower() for v in _multi(t, 'variables')]
                ts = [(type_name.get(x) or '').lower() for x in _multi(t, 'variableTypes')]
                ts += [''] * max(0, len(vs) - len(ts))
                return ('exists' if s == 'PDDL_Exists' else 'forall', tuple(zip(vs, ts)), canon(_single(t, 'scope')))
            if s == 'PDDL_ConditionalEffect':
                return ('when', canon(_single(t, 'condition')), canon(_single(t, 'effect')))
            if s == 'PDDL_Comparison':
                op_raw = _single(t, 'operator')
                op_name = m.name(op_raw) or op_raw
                return ('cmp', CMP_PDDL.get(op_name, op_name), canon(_single(t, 'left')), canon(_single(t, 'right')))
            if s == 'PDDL_PredicateAtom':
                ref_preds.add(t['predicate'])
                return ('atom', (preds[t['predicate']]['name'],) + tuple(t.get('_arguments', [])))
            if s == 'PDDL_FunctionAtom':
                ref_funcs.add(t['function'])
                return ('atom', (funcs[t['function']]['name'],) + tuple(t.get('_arguments', [])))
            if s == 'PDDL_Literal':
                v = t.get('value')
                return ('lit', strip_num(v) if v is not None else None)
            if s == 'PDDL_ArithmeticExpression':
                return num_term(m, eid, funcs, ref_funcs)
            if s in NUM_EFFECT:
                ref_funcs.add(t['target'])
                return (NUM_EFFECT[s], (funcs[t['target']]['name'],) + tuple(_multi(t, 'targetArguments')),
                        canon(_single(t, NUM_VALUE_TAG.get(s, 'value'))))
            if s == 'PDDL_Increase':
                ref_funcs.add(t['target'])
                return ('increase-nested', (funcs[t['target']]['name'],) + tuple(_multi(t, 'targetArguments')),
                        canon(_single(t, 'value')))
        return ('NOT-CHECKABLE', '+'.join(s for s, _ in stereos) or (m.name(eid) or str(eid)))

    def walk(eid, neg=False):
        hit = False
        for s, t in m.stereos_of(eid):
            if s == 'PDDL_And':
                hit = True
                for op in t.get('operands', '').split():
                    walk(op, neg)
            elif s == 'PDDL_Not':
                hit = True
                walk(t.get('operand'), not neg)
            elif s == 'PDDL_PredicateAtom':
                hit = True
                ref_preds.add(t['predicate'])
                atom = (preds[t['predicate']]['name'],) + tuple(t.get('_arguments', []))
                out.add(('not', atom) if neg else ('atom', atom))
            elif s == 'PDDL_Increase':
                hit = True
                ref_funcs.add(t['target'])
                vrepr = None
                if any(s2 == 'PDDL_ArithmeticExpression' for s2, _ in m.stereos_of(t.get('value'))):
                    vrepr = canon(t.get('value'))
                for s2, t2 in m.stereos_of(t.get('value')):
                    if s2 == 'PDDL_FunctionAtom':
                        ref_funcs.add(t2['function'])
                        vrepr = (funcs[t2['function']]['name'],) + tuple(t2.get('_arguments', []))
                    elif s2 == 'PDDL_Literal':
                        vrepr = ('lit', strip_num(t2.get('value')))
                out.add(('increase', (funcs[t['target']]['name'],) + tuple(_multi(t, 'targetArguments')), vrepr))
            elif s in ('PDDL_Or', 'PDDL_Imply', 'PDDL_Exists', 'PDDL_Forall', 'PDDL_ConditionalEffect',
                       'PDDL_Comparison', 'PDDL_FunctionAtom', 'PDDL_Literal') or s in NUM_EFFECT:
                hit = True                       # nested operators stay one structured entry
                lit = canon(eid)
                out.add(('not', lit) if neg else lit)
        if not hit and m.stereos_of(eid):
            out.add(('NOT-CHECKABLE', '+'.join(s for s, _ in m.stereos_of(eid))))
    if fid:
        walk(fid)
    return out


def parse_param_string(s):
    """'?s - system ?from - pos' -> [('?s', 'system'), ('?from', 'pos')]"""
    return typed_list(s.split())


# ------------------------------------------------------------------------------------ PDDL side
def sexp(text):
    text = re.sub(r';[^\n]*', '', text)
    toks = text.replace('(', ' ( ').replace(')', ' ) ').split()

    def rd(i):
        if toks[i] == '(':
            lst = []
            i += 1
            while toks[i] != ')':
                node, i = rd(i)
                lst.append(node)
            return lst, i + 1
        return toks[i], i + 1
    out, i = [], 0
    while i < len(toks):
        node, i = rd(i)
        out.append(node)
    return out


def typed_list(toks):
    out, pend, i = [], [], 0
    while i < len(toks):
        if toks[i] == '-':
            out += [(v, toks[i + 1]) for v in pend]
            pend, i = [], i + 2
        else:
            pend.append(toks[i])
            i += 1
    return out + [(v, 'object') for v in pend]


def norm_formula(f):
    """Generated formula -> set of normalized literals, as on the model side."""
    out = set()

    def walk(node, neg=False):
        if not isinstance(node, list) or not node:
            return
        h = node[0]
        if h == 'and':
            for sub in node[1:]:
                walk(sub, neg)
        elif h == 'not':
            walk(node[1], not neg)
        elif h == 'increase':
            tgt = tuple(node[1]) if isinstance(node[1], list) else (node[1],)
            val = tuple(node[2]) if isinstance(node[2], list) else ('lit', strip_num(node[2]))
            if isinstance(node[2], list) and node[2] and node[2][0] in ('+', '-', '*', '/'):
                val = canon_gen(node[2])
            elif isinstance(node[2], list) and any(isinstance(x, list) for x in node[2]):
                val = ('NOT-CHECKABLE', 'arithmetic')
            out.add(('increase', tgt, val))
        elif h in GEN_NESTED:
            lit = canon_gen(node)
            out.add(('not', lit) if neg else lit)
        elif any(isinstance(x, list) for x in node):
            out.add(('NOT-CHECKABLE', str(h)))
        else:
            atom = tuple(node)
            out.add(('not', atom) if neg else ('atom', atom))
    walk(f)
    return out


def parse_pddl(domain_text, problem_text):
    actions = {}
    dom = {'actions': actions}
    d = sexp(domain_text)[0]
    dom['name'] = d[1][1]
    for sec in d[2:]:
        h = sec[0]
        if h == ':requirements':
            dom['requirements'] = sec[1:]
        elif h == ':types':
            dom['types'] = dict(typed_list(sec[1:]))
        elif h == ':constants':
            dom['constants'] = dict(typed_list(sec[1:]))
        elif h == ':predicates':
            dom['predicates'] = {p[0]: [t for _, t in typed_list(p[1:])] for p in sec[1:]}
        elif h == ':functions':
            toks, i = sec[1:], 0
            dom['functions'] = {}
            while i < len(toks):
                if isinstance(toks[i], list):
                    nm, params, rng = toks[i][0], [t for _, t in typed_list(toks[i][1:])], None
                    if i + 2 < len(toks) and toks[i + 1] == '-':
                        rng = toks[i + 2]
                        i += 2
                    dom['functions'][nm] = {'params': params, 'range': rng}
                i += 1
        elif h == ':action':
            a = {'name': sec[1]}
            body = sec[2:]
            for k in range(0, len(body), 2):
                key, val = body[k], body[k + 1]
                if key == ':parameters':
                    a['params'] = typed_list(val)
                elif key == ':precondition':
                    a['pre'] = norm_formula(val)
                elif key == ':effect':
                    a['eff'] = norm_formula(val)
            actions[a['name']] = a
    p = sexp(problem_text)[0]
    prob = {'name': p[1][1]}
    for sec in p[2:]:
        h = sec[0]
        if h == ':domain':
            prob['domain'] = sec[1]
        elif h == ':objects':
            prob['objects'] = dict(typed_list(sec[1:]))
        elif h == ':init':
            init = set()
            for f in sec[1:]:
                if f[0] == '=':
                    init.add(('=', tuple(f[1]) if isinstance(f[1], list) else (f[1],), f[2]))
                elif f[0] == 'not' and len(f) == 2 and isinstance(f[1], list):
                    init.add(('not', tuple(f[1])))
                else:
                    init.add(('atom', tuple(f)))
            prob['init'] = init
        elif h == ':goal':
            prob['goal'] = norm_formula(sec[1])
        elif h == ':metric':
            expr = sec[2]
            prob['metric'] = (sec[1], expr[0] if isinstance(expr, list) else expr)
    return dom, prob


# ----------------------------------------------------------------------------------- comparison
def compare(exp, dom, prob):
    """Returns (findings, stats); a finding is (category, direction, text)."""
    findings, stats = [], {}

    def cover(cat, expected, actual):
        e, a = set(expected), set(actual)
        for k in sorted(e - a, key=str):
            findings.append((cat, 'source', 'missing in the generated files: %s' % (k,)))
        declared = exp.get('declared', {}).get(cat, set())
        for k in sorted(a - e, key=str):
            name = k[0] if isinstance(k, tuple) and k else k
            if str(name).lower() in declared:
                findings.append((cat, 'target', 'declared in the model but not used: %s' % (k,)))
            else:
                findings.append((cat, 'target', 'orphan, no model source: %s' % (k,)))
        stats[cat] = {'expected': len(e), 'found': len(e & a), 'actual': len(a), 'justified': len(a & e)}

    cover('requirements', exp['requirements'], dom.get('requirements', []))
    cover('types', [(t['name'], t['parent']) for t in exp['types'].values()], list(dom.get('types', {}).items()))
    cover('predicates', [(p['name'], tuple(t for _, t in p['params'])) for p in exp['predicates'].values()],
          [(n, tuple(ts)) for n, ts in dom.get('predicates', {}).items()])
    cover('functions', [(f['name'], tuple(t for _, t in f['params'])) for f in exp['functions'].values()],
          [(n, tuple(v['params'])) for n, v in dom.get('functions', {}).items()])
    for nm, a in sorted(exp['actions'].items()):
        g = dom['actions'].get(nm)
        if g is None:
            findings.append(('actions', 'source', 'missing in the generated files: action %s (Mode %s, source %r)'
                             % (nm, a['mode'], a['srcname'])))
            continue
        if list(a['params']) != list(g.get('params', [])):
            findings.append(('actions', 'semantic', 'action %s: parameters differ, model %s vs. generated %s'
                             % (nm, a['params'], g.get('params'))))
        for what, e_set, g_set in (('precondition', a['pre'], g.get('pre', set())), ('effect', a['eff'], g.get('eff', set()))):
            for lit in sorted(e_set - g_set, key=str):
                findings.append(('actions', 'semantic', 'action %s: %s literal missing in the generated files: %s' % (nm, what, lit)))
            for lit in sorted(g_set - e_set, key=str):
                findings.append(('actions', 'semantic', 'action %s: %s literal without model source: %s' % (nm, what, lit)))
    for nm in sorted(set(dom['actions']) - set(exp['actions'])):
        findings.append(('actions', 'target', 'orphan, no model source: action %s' % nm))
    stats['actions'] = {'expected': len(exp['actions']), 'found': len(set(exp['actions']) & set(dom['actions'])),
                        'actual': len(dom['actions']), 'justified': len(set(dom['actions']) & set(exp['actions']))}
    if exp.get('constants') or dom.get('constants'):
        cover('constants', [(c['name'], c['type']) for c in exp['constants'].values()],
              list(dom.get('constants', {}).items()))
    cover('objects', [(o['name'], o['type']) for o in exp['objects'].values()], list(prob.get('objects', {}).items()))
    cover('init', exp['init'], prob.get('init', set()))
    cover('goal', exp['goal'], prob.get('goal', set()))
    if exp['metric'] and prob.get('metric') != exp['metric']:
        findings.append(('metric', 'semantic', 'metric: model %s vs. generated %s' % (exp['metric'], prob.get('metric'))))
    if prob.get('domain') != exp['domain_name']:
        findings.append(('problem', 'semantic', ':domain refers to %r, expected %r' % (prob.get('domain'), exp['domain_name'])))
    return findings, stats


def self_test(exp, dom, prob):
    """Three injected faults; each must be found."""
    results = []
    d1 = copy.deepcopy(dom)
    victim = sorted(d1['actions'])[0]
    del d1['actions'][victim]
    f1, _ = compare(exp, d1, prob)
    results.append(('omission (action %s removed)' % victim, any(c == 'actions' and r == 'source' for c, r, _ in f1)))
    p2 = copy.deepcopy(prob)
    p2['init'] = set(p2['init']) | {('atom', ('ghost-pred', 'nowhere1'))}
    f2, _ = compare(exp, dom, p2)
    results.append(('addition (init fact injected)', any(c == 'init' and r == 'target' for c, r, _ in f2)))
    d3 = copy.deepcopy(dom)
    for a in d3['actions'].values():
        for lit in sorted(a.get('pre', set()), key=str):
            if lit[0] == 'atom' and len(lit[1]) == 3:
                a['pre'] = set(a['pre'])
                a['pre'].discard(lit)
                a['pre'].add(('atom', (lit[1][0], lit[1][2], lit[1][1])))
                break
        else:
            continue
        break
    f3, _ = compare(exp, d3, prob)
    results.append(('wrong binding (arguments swapped)', any(c == 'actions' and r == 'semantic' for c, r, _ in f3)))
    return results


# --------------------------------------------------------------------------------------- report
def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--model', required=True, help='annotated model (.mdzip)')
    ap.add_argument('--domain', required=True, help='generated domain (.pddl)')
    ap.add_argument('--problem', required=True, help='generated problem (.pddl)')
    ap.add_argument('--label', default='', help='name of the case in the report')
    ap.add_argument('--out-dir', default='.', help='folder for the report files')
    ap.add_argument('--self-test', action='store_true', help='inject three faults and check that all three are found')
    args = ap.parse_args()

    def sha256(path):
        return hashlib.sha256(open(path, 'rb').read()).hexdigest()

    xml_bytes = zipfile.ZipFile(args.model).read('com.nomagic.magicdraw.uml_model.model')
    domain_text = open(args.domain, encoding='utf-8').read()
    problem_text = open(args.problem, encoding='utf-8').read()
    dom, prob = parse_pddl(domain_text, problem_text)
    m = Model(xml_bytes)
    exp = build_expected(m, dom['name'], prob['name'])
    findings, stats = compare(exp, dom, prob)
    label = args.label or dom['name']

    lines = ['# Traceability check: %s' % label, '',
             '| Input | File | SHA-256 |', '|---|---|---|',
             '| Model | `%s` | `%s` |' % (os.path.basename(args.model), sha256(args.model)),
             '| Domain | `%s` | `%s` |' % (os.path.basename(args.domain), sha256(args.domain)),
             '| Problem | `%s` | `%s` |' % (os.path.basename(args.problem), sha256(args.problem)), '',
             '## Coverage', '', '| Category | Source coverage | Target justification |', '|---|---|---|']
    tot = [0, 0, 0, 0]
    for cat, s in stats.items():
        tot = [tot[0] + s['found'], tot[1] + s['expected'], tot[2] + s['justified'], tot[3] + s['actual']]
        lines.append('| %s | %d/%d | %d/%d |' % (cat, s['found'], s['expected'], s['justified'], s['actual']))
    lines += ['| **total** | **%d/%d** | **%d/%d** |' % tuple(tot), '', '## Actions', '',
              '| Action | Mode | Source call(s) |', '|---|---|---|']
    for nm, a in sorted(exp['actions'].items()):
        lines.append('| %s | %s | %s |' % (nm, a['mode'], ' + '.join('`%s`' % q for q in a.get('srcnames') or [a['srcname']])))
    lines += ['', '## Findings (%d)' % len(findings), '']
    lines += ['- **[%s/%s]** %s' % f for f in findings] or ['None. Every model element appears in the generated files, '
                                                          'and every generated element has a model source.']
    if exp['warnings']:
        lines += ['', '## Warnings'] + ['- ' + w for w in exp['warnings']]
    st = self_test(exp, dom, prob) if args.self_test else []
    if args.self_test:
        lines += ['', '## Self-test (%d/3)' % sum(1 for _, hit in st if hit), '']
        lines += ['- %s: %s' % (lbl, 'found' if hit else 'not found') for lbl, hit in st]
    os.makedirs(args.out_dir, exist_ok=True)
    md = os.path.join(args.out_dir, 'TRACE_%s.md' % label)
    open(md, 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
    json.dump({'stats': stats, 'findings': [{'category': c, 'direction': d, 'text': t} for c, d, t in findings],
               'self_test': [{'fault': lbl, 'found': hit} for lbl, hit in st]},
              open(os.path.join(args.out_dir, 'TRACE_%s.json' % label), 'w', encoding='utf-8'), indent=1)
    print('Report: %s' % md)
    print('Findings: %d  source %d/%d  target %d/%d' % ((len(findings),) + tuple(tot)))
    for lbl, hit in st:
        print('  self-test %s: %s' % (lbl, 'OK' if hit else 'failed'))
    if args.self_test and not all(hit for _, hit in st):
        sys.exit(2)
    sys.exit(1 if findings else 0)


if __name__ == '__main__':
    main()
