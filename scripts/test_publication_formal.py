#!/usr/bin/env python3
"""Focused negative controls for selected formal evidence; no Lean or SAT calls."""
import copy
import json
import re
from pathlib import Path, PurePosixPath
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'reproduce'))
import publication_formal_evidence as evidence


class ArchiveFixture:
    def __init__(self, root, values, paths, custody):
        self.formal = PurePosixPath('/old/formal')
        self.manifest = {'build_result': '/old/BUILD_RESULT.json', 'bindings': {'base': '/old/base/RESULT.json'}}
        self.values = values; self.paths = paths; self.custody = custody

    def json(self, name):
        return self.values[str(name)]

    def get(self, name):
        return self.paths[str(name)]


class FormalEvidenceTests(unittest.TestCase):
    def test_authority_pins_are_complete_sha256(self):
        values = [evidence.ORIGINAL_NATIVE_SHA, evidence.ORIGINAL_FORMAL_SHA, evidence.BASE_SHA,
                  *evidence.MANIFESTS.values(), *(item[1] for item in evidence.EMITTERS.values()),
                  *(item[2] for item in evidence.CATALOGUES.values())]
        self.assertTrue(all(re.fullmatch('[0-9a-f]{64}', value) for value in values))

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.root = Path(self.temp.name).resolve()
        self.formal = self.root / 'formal'; self.formal.mkdir()
        source_sha = '1' * 64; compiler_sha = '2' * 64
        self.source = {'modules': {'UniformK60.Core': {'sha256': source_sha, 'imports': ['Mathlib.Test']}}}
        (self.formal / 'SOURCE_MANIFEST.json').write_text(json.dumps(self.source))
        self.custody = {
            '/old/lib/UniformK60/Core.olean': {'sha256': '3' * 64, 'bytes': 10},
            '/old/lib/UniformK60/Core.olean.private': {'sha256': '4' * 64, 'bytes': 20},
            '/deps/Mathlib/Test.olean': {'sha256': '5' * 64, 'bytes': 30},
        }
        artifacts = [{'path': k, **v} for k, v in self.custody.items() if k.startswith('/old/lib/')]
        external = {'path': '/deps/Mathlib/Test.olean', **self.custody['/deps/Mathlib/Test.olean']}
        baseline = {'sources': {'UniformK60.Core': {'sha256': source_sha}},
                    'modules': [{'module': 'UniformK60.Core', 'artifacts': artifacts,
                                 'imports': {'Mathlib.Test': [external]},
                                 'command': ['/usr/bin/nice', '-n', '10', '/lean']}],
                    'compiler_sha256': compiler_sha, 'lean_path': '/old/lib:/deps'}
        build = self.root / 'BUILD_RESULT.json'; build.write_text(json.dumps(baseline))
        receipt = {'passed': True, 'build_result': '/old/BUILD_RESULT.json',
                   'build_result_sha256': evidence.pin(build)['sha256'], 'compiler_sha256': compiler_sha,
                   'command': ['/usr/bin/nice', '-n', '10', '/lean', '-j1', '--run', '/old/formal/reproduce/EmitBase.lean'],
                   'exit_code': 0}
        recpath = self.root / 'RESULT.json'; recpath.write_text(json.dumps(receipt))
        emitter = self.root / 'EmitBase.lean'
        emitter.write_bytes((Path(__file__).resolve().parents[1] / 'formal/reproduce/EmitBase.lean').read_bytes())
        values = {'/old/BUILD_RESULT.json': baseline, '/old/base/RESULT.json': receipt}
        paths = {'/old/BUILD_RESULT.json': build, '/old/base/RESULT.json': recpath,
                 '/old/formal/reproduce/EmitBase.lean': emitter}
        for name in ('lean-base.body', 'emit.log'):
            path = self.root / name; path.write_bytes(b'accepted emission bytes\n')
            paths['/old/base/' + name] = path
        archive = ArchiveFixture(self.root, values, paths, self.custody)
        self.context = {'baseline_archive': archive, 'formal': self.formal, 'logical_run': '/new',
                        'build': {'reused_modules': ['UniformK60.Core']},
                        'compiler': {'path': '/lean', 'sha256': compiler_sha},
                        'artifacts': {k.replace('/old/lib/', '/new/lib/'): v for k, v in self.custody.items()}}
        self.archive = archive

    def tearDown(self):
        self.temp.cleanup()

    def test_identical_execution_inputs(self):
        result = evidence.emission_reuse(self.context, 'base')
        self.assertEqual(result['project_modules'], ['UniformK60.Core'])
        self.assertEqual(result['recorded_artifact_count'], 3)

    def test_changed_compiler(self):
        self.context['compiler']['sha256'] = '0' * 64
        with self.assertRaises(ValueError): evidence.emission_reuse(self.context, 'base')

    def test_changed_emitter(self):
        self.archive.paths['/old/formal/reproduce/EmitBase.lean'].write_text('import UniformK60.Core\n')
        with self.assertRaises(ValueError): evidence.emission_reuse(self.context, 'base')

    def test_changed_options(self):
        self.archive.values['/old/base/RESULT.json']['command'][4] = '-j8'
        with self.assertRaises(ValueError): evidence.emission_reuse(self.context, 'base')

    def test_changed_project_companion(self):
        self.context['artifacts']['/new/lib/UniformK60/Core.olean.private'] = {'sha256': '0' * 64, 'bytes': 20}
        with self.assertRaises(ValueError): evidence.emission_reuse(self.context, 'base')

    def test_missing_project_companion(self):
        del self.context['artifacts']['/new/lib/UniformK60/Core.olean.private']
        with self.assertRaises(ValueError): evidence.emission_reuse(self.context, 'base')

    def test_changed_external_import(self):
        self.context['artifacts']['/deps/Mathlib/Test.olean'] = {'sha256': '0' * 64, 'bytes': 30}
        with self.assertRaises(ValueError): evidence.emission_reuse(self.context, 'base')

    def test_changed_source(self):
        self.source['modules']['UniformK60.Core']['sha256'] = '0' * 64
        (self.formal / 'SOURCE_MANIFEST.json').write_text(json.dumps(self.source))
        with self.assertRaises(ValueError): evidence.emission_reuse(self.context, 'base')

    def test_dependency_was_rebuilt(self):
        self.context['build']['reused_modules'] = []
        with self.assertRaises(ValueError): evidence.emission_reuse(self.context, 'base')

    def test_mutated_retained_bytes(self):
        path = self.root / 'emission.cnf'; path.write_bytes(b'p cnf 1 1\n1 0\n'); expected = evidence.pin(path)
        path.write_bytes(b'p cnf 1 1\n-1 0\n')
        with self.assertRaises(ValueError): evidence.checked(path, expected)

    def test_changed_composite_dependency_closure(self):
        names = {'UniformK60.BalancedC2Normalize', 'UniformK60.BalancedEncodingBalance',
                 'UniformK60.ExactInputs', 'UniformK60.FiniteBoundary', evidence.TARGET}
        manifest = {'modules': {n: {'sha256': '1' * 64, 'imports': []} for n in names}}
        self.assertEqual(evidence.changed_closure(manifest, {'sources': {}}), names)
        manifest['modules']['UniformK60.Core'] = {'sha256': '1' * 64, 'imports': []}
        with self.assertRaises(ValueError): evidence.changed_closure(manifest, {'sources': {}})


if __name__ == '__main__':
    unittest.main()
