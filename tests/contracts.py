#!/usr/bin/env python3
"""Exercise the contract checker with changed APIs and internal proof helpers."""
import contextlib
import copy
import hashlib
import importlib.util
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('contracts', ROOT / 'scripts/check-contracts.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def declaration(name, *, kind='theorem', value=None, instance=False):
    return {'name': name, 'contract': {
        'kind': kind, 'levels': [], 'type': 'original type', 'value': value,
        'reducibility': 'opaque', 'instance': instance, 'unsafe': False, 'partial': False,
    }, 'directSorry': False, 'dependencies': [], 'axioms': []}


def fingerprints(rows):
    result = {}
    for row in rows:
        contract = dict(row['contract'])
        for field in ('type', 'value'):
            if contract[field] is not None:
                contract[field] = hashlib.sha256(contract[field].encode()).hexdigest()
        result[row['name']] = contract
    return result


class ContractChecks(unittest.TestCase):
    def setUp(self):
        self.theorem = declaration('Parikh.grammar_image')
        self.definition = declaration('Parikh.counts', kind='definition', value='original body')
        self.helper = declaration('Parikh.grammar_image._simp_1_2')
        self.original = [self.theorem, self.definition, self.helper]

    def check(self, current, *, original=None, proposed=None):
        """Use exported-declaration fixtures; no Lean build is needed for policy tests."""
        with tempfile.TemporaryDirectory(prefix='parikh-contract-test-') as directory:
            root = Path(directory)
            (root / '.lake').mkdir()
            (root / 'maintenance/contracts').mkdir(parents=True)
            (root / 'Parikh.lean').write_text('-- fixture\n')
            pins = {}
            for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
                (root / name).write_text(name)
                pins[name] = hashlib.sha256(name.encode()).hexdigest()
            baseline = {'pins': pins, 'declarations': fingerprints(
                self.original if original is None else original)}
            proposal = {'pins': pins, 'declarations': checker.compatibility_declarations(
                fingerprints(current if proposed is None else proposed))}
            (root / '.lake/contract-audit.json').write_text(json.dumps(current))
            (root / 'maintenance/contracts/proposed.json').write_text(json.dumps(proposal))
            (root / 'maintenance/contracts/baseline.json').write_text(json.dumps(
                {'accepted_commit': 'accepted-skeleton'}))
            (root / 'maintenance/contracts/obligations.json').write_text(json.dumps({
                'sorry': [], 'temporary_axioms': [], 'dependent_on_unresolved': [],
                'compiler_generated_partial': [],
            }))
            prior = subprocess.CompletedProcess([], 0, stdout=json.dumps(baseline))
            with patch.object(checker, 'ROOT', root), patch.object(checker, 'run'), \
                    patch.object(checker.subprocess, 'check_output', return_value=json.dumps(baseline).encode()), \
                    patch.object(checker.subprocess, 'run', return_value=prior), \
                    patch.object(sys, 'argv', ['check-contracts.py', '--final']), \
                    contextlib.redirect_stdout(io.StringIO()):
                checker.main()

    def test_removed_internal_helper(self):
        self.check([self.theorem, self.definition])

    def test_regenerated_internal_helper(self):
        for name in ('Parikh.grammar_image._simp_9_4',
                     'Parikh.grammar_image._proof_1_3',
                     '_private.Parikh.GrammarImage.0.helper'):
            with self.subTest(name=name):
                helper = declaration(name)
                helper['contract']['type'] = 'new helper type'
                self.check([self.theorem, self.definition, helper])

    def test_removed_mathematical_theorem(self):
        with self.assertRaisesRegex(SystemExit, 'changed: Parikh.grammar_image'):
            self.check([self.definition, self.helper])

    def test_changed_theorem_signature(self):
        theorem = copy.deepcopy(self.theorem)
        theorem['contract']['type'] = 'extra assumption'
        with self.assertRaisesRegex(SystemExit, 'changed: Parikh.grammar_image'):
            self.check([theorem, self.definition, self.helper])

    def test_changed_definition_body(self):
        definition = copy.deepcopy(self.definition)
        definition['contract']['value'] = 'different meaning'
        with self.assertRaisesRegex(SystemExit, 'changed: Parikh.counts'):
            self.check([self.theorem, definition, self.helper])

    def test_internal_definition_is_protected(self):
        old = declaration('Parikh.counts._helper', kind='definition', value='body')
        new = copy.deepcopy(old)
        new['contract']['value'] = 'changed body'
        with self.assertRaisesRegex(SystemExit, 'changed: Parikh.counts._helper'):
            self.check([self.theorem, new], original=[self.theorem, old])

    def test_internal_instance_is_protected(self):
        old = declaration('Parikh._instance', instance=True)
        new = copy.deepcopy(old)
        new['contract']['instance'] = False
        with self.assertRaisesRegex(SystemExit, 'changed: Parikh._instance'):
            self.check([self.theorem, new], original=[self.theorem, old])

    def test_new_mathematical_declaration_needs_manifest_entry(self):
        extra = declaration('Parikh.new_result')
        with self.assertRaisesRegex(SystemExit, 'compatibility manifest'):
            self.check([*self.original, extra], proposed=self.original)

    def test_internal_helper_with_unexpected_axiom(self):
        helper = copy.deepcopy(self.helper)
        helper['axioms'] = ['customAxiom']
        with self.assertRaisesRegex(SystemExit, 'Unrecognized proof dependencies'):
            self.check([self.theorem, self.definition, helper])

    def test_internal_helper_with_placeholder(self):
        helper = copy.deepcopy(self.helper)
        helper['directSorry'] = True
        helper['axioms'] = ['sorryAx']
        with self.assertRaisesRegex(SystemExit, 'Direct hole allowlist mismatch'):
            self.check([self.theorem, self.definition, helper])

    def test_internal_helper_with_transitive_placeholder(self):
        helper = copy.deepcopy(self.helper)
        helper['axioms'] = ['sorryAx']
        with self.assertRaisesRegex(SystemExit, 'Transitive unresolved-dependency'):
            self.check([self.theorem, self.definition, helper])

    def test_internal_helper_with_unsafe_code(self):
        helper = copy.deepcopy(self.helper)
        helper['contract']['unsafe'] = True
        with self.assertRaisesRegex(SystemExit, 'Unsafe project declaration'):
            self.check([self.theorem, self.definition, helper])


if __name__ == '__main__':
    unittest.main()
