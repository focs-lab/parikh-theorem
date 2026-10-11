#!/usr/bin/env python3
"""Exercise the CLI process, JSON boundary and representative grammar outputs."""
import copy
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLI = ROOT / 'bin/parikh'


def invoke(args=(), *, text=None, cwd=ROOT):
    return subprocess.run([str(CLI), *args], input=text, text=True,
                          capture_output=True, cwd=cwd, timeout=30)


def success(args=(), *, grammar=None, cwd=ROOT):
    result = invoke(args, text=None if grammar is None else json.dumps(grammar), cwd=cwd)
    assert result.returncode == 0, result.stderr
    assert result.stderr == '', result.stderr
    return json.loads(result.stdout)


def reject(grammar=None, *, text=None, args=(), diagnostic):
    result = invoke(args, text=json.dumps(grammar) if grammar is not None else text)
    assert result.returncode != 0, result.stdout
    assert result.stdout == '', result.stdout
    assert diagnostic in result.stderr, result.stderr


def grammar(d=0, n=1, rules=None):
    return {'terminalCount': d, 'nonterminalCount': n, 'initial': 0,
            'rules': [] if rules is None else rules}


def main():
    help_result = invoke(['--help'])
    assert help_result.returncode == 0 and 'Usage:' in help_result.stdout
    assert help_result.stderr == ''
    reject(args=['--unknown'], diagnostic='unknown option')
    reject(args=['one.json', 'two.json'], diagnostic='at most one')
    reject(args=['/definitely-missing-parikh-grammar.json'], diagnostic='parikh:')

    unary = json.loads((ROOT / 'examples/cli/unary.json').read_text())
    expected = {'terminalCount': 1, 'components': [
        {'base': [0], 'periods': []},
        {'base': [1], 'periods': [[1]]},
        {'base': [2], 'periods': [[2]]},
        {'base': [3], 'periods': [[1], [2]]},
    ]}
    assert success(['examples/cli/unary.json']) == expected
    assert success(['-'], grammar=unary) == expected
    assert success(grammar=unary) == expected
    with tempfile.TemporaryDirectory(prefix='parikh-cli-') as directory:
        path = Path(directory) / 'grammar with spaces.json'
        path.write_text(json.dumps(unary))
        assert success([path.name], cwd=directory) == expected

    assert success(['examples/cli/empty.json']) == {'terminalCount': 0, 'components': []}
    zero = {'terminalCount': 0, 'components': [{'base': [], 'periods': []}]}
    assert success(['examples/cli/epsilon.json']) == zero

    epsilon = {'input': 0, 'output': []}
    silent = {'input': 0, 'output': [{'nonterminal': 0}]}
    silent_output = success(grammar=grammar(rules=[epsilon, silent]))
    assert [len(c['periods']) for c in silent_output['components']] == [0, 1, 1, 2]
    assert success(grammar=grammar(rules=[epsilon, silent, silent])) == silent_output
    assert success(grammar=grammar(n=2, rules=[epsilon])) == zero  # Unused declared label.
    assert success(grammar=grammar(n=2, rules=[epsilon,
        {'input': 1, 'output': [{'nonterminal': 1}]}])) == zero  # Unreachable cycles.

    # Coordinate order matters: the only emitted letter has terminal label 1.
    assert success(grammar=grammar(d=2, rules=[
        {'input': 0, 'output': [{'terminal': 1}]}])) == {
            'terminalCount': 2, 'components': [{'base': [0, 1], 'periods': []}]}

    reject(text='{', diagnostic='invalid JSON')
    reject(text='[]', diagnostic='object expected')
    bad = grammar()
    bad['nonterminalCount'] = 0
    reject(bad, diagnostic='nonterminalCount: must be at least 1')
    bad = grammar()
    bad['initial'] = 1
    reject(bad, diagnostic='initial: label 1 must be below 1')
    for value in (-1, 1.5, '1', True):
        bad = grammar()
        bad['terminalCount'] = value
        reject(bad, diagnostic='terminalCount: expected a nonnegative integer')
    bad = grammar()
    del bad['rules']
    reject(bad, diagnostic='property not found: rules')
    bad = grammar()
    bad['terminalCounnt'] = 0
    reject(bad, diagnostic="unknown field 'terminalCounnt'")
    reject(grammar(rules={}), diagnostic='rules: array expected')
    reject(grammar(rules=[{'input': 1, 'output': []}]), diagnostic='rules[0].input: label 1')
    reject(grammar(rules=[{'input': 0, 'output': [{'terminal': 0}]}]),
           diagnostic='rules[0].output[0].terminal: label 0 must be below 0')
    reject(grammar(rules=[{'input': 0, 'output': [{'nonterminal': 1}]}]),
           diagnostic='rules[0].output[0].nonterminal: label 1 must be below 1')
    reject(grammar(rules=[{'input': 0, 'output': [{'terminal': 0, 'nonterminal': 0}]}]),
           diagnostic="expected exactly one 'terminal' or 'nonterminal' field")
    reject(grammar(rules=[{'input': 0, 'output': [{'typo': 0}]}]), diagnostic='expected exactly one')
    reject(grammar(rules=[{'input': 0, 'output': [0]}]), diagnostic='object expected')
    reject(grammar(rules=[{'input': 0, 'output': 'epsilon'}]), diagnostic='output: array expected')
    bad = copy.deepcopy(unary)
    bad['rules'][0]['extra'] = 1
    reject(bad, diagnostic="unknown field 'extra'")
    print('CLI end-to-end checks passed.')


if __name__ == '__main__':
    main()
