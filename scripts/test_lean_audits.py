"""Adversarial controls for source/manifest and small-target audits; no Lean."""
import copy
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_lean_sources as source
from lean_ci import validate_report, THEOREMS, MODULES, TARGET, audit_run, copy_receipts, check_small_closure

PACKAGE = Path(os.environ.get('RAMSEY_CI_TEST_FORMAL', source.FORMAL))


def pin(path, root):
    payload = path.read_bytes()
    return {'path': path.relative_to(root).as_posix(), 'bytes': len(payload),
            'sha256': hashlib.sha256(payload).hexdigest()}


def report():
    return '\n'.join(f"'{name}' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
                     for name in sorted(THEOREMS))


class SourceControls(unittest.TestCase):
    def test_comments_and_strings_masked(self):
        self.assertFalse(source.violations('/- sorry /- axiom -/ admit -/\n-- unsafe\ndef x := "native_decide"'))

    def test_real_escapes_rejected(self):
        for text in ('private axiom x : False', '@[attr] unsafe def f := 1', 'by sorry',
                     'by native_decide', 'by admit', 'partial def f := f',
                     'set_option debug.skipKernelTC true', '#eval IO.println "hi"',
                     'run_elab pure ()', 'Lean.ofReduceBool true', '@[implemented_by x] def y := 1',
                     'theorem bad : False := sorryAx False true', 'open Lean\n#check ofReduceBool',
                     '#check ofReduceNat', '#check trustCompiler', '#check «sorryAx»',
                     '#check Lean.«ofReduceBool»'):
            with self.subTest(text=text):
                self.assertTrue(source.violations(text))

    def test_unclosed_comment_or_string_rejected(self):
        for text in ('/- hidden', 'def x := "hidden', 'def «hidden'):
            with self.assertRaises(ValueError):
                source.violations(text)

    def test_exact_helper_exception_only(self):
        payload = ('\n' * 39 + '\n'.join(source.HELPER_LINES.values()) + '\n').encode()
        with patch.object(source, 'HELPER_SHA', hashlib.sha256(payload).hexdigest()):
            self.assertFalse(source.proof_violations(source.HELPER, payload))
            self.assertTrue(source.proof_violations('src/Other.lean', payload))
            with self.assertRaises(ValueError):
                source.proof_violations(source.HELPER, payload + b'unsafe def more := 1\n')

    def test_released_helper_is_exactly_reviewed(self):
        self.assertFalse(source.proof_violations(source.HELPER, (PACKAGE / source.HELPER).read_bytes()))

    def test_full_build_acceptance_pin_is_exact(self):
        source.require_accepted_manifest('a' * 64, 'a' * 64)
        for accepted in (None, '', 'b' * 64):
            with self.assertRaises(ValueError):
                source.require_accepted_manifest('a' * 64, accepted)

    def test_accepted_pin_file_is_mandatory_and_exact(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'ACCEPTED_MATH_MANIFEST.sha256'
            with self.assertRaises(ValueError): source.read_accepted_manifest_pin(path)
            for value in ('a' * 64, 'a' * 64 + '\r\n', 'A' * 64 + '\n', 'a' * 64 + '\nextra'):
                path.write_bytes(value.encode())
                with self.assertRaises(ValueError): source.read_accepted_manifest_pin(path)
            path.write_bytes(('a' * 64 + '\n').encode())
            self.assertEqual(source.read_accepted_manifest_pin(path), 'a' * 64)
            with self.assertRaises(ValueError):
                source.require_accepted_manifest('b' * 64, source.read_accepted_manifest_pin(path))

    def test_duplicate_json_keys_rejected(self):
        with self.assertRaises(ValueError):
            source.strict_json('{"modules": {}, "modules": {}}')


class ManifestControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'src').mkdir()
        for name in source.CONTROL_FILES:
            (self.root / name).write_bytes((PACKAGE / name).read_bytes())
        (self.root / 'src/A.lean').write_text('import Init\ndef payload := include_str "payload.cnf"\n')
        (self.root / 'src/payload.cnf').write_text('p cnf 0 0\n')
        self.manifest = {
            'toolchain': 'leanprover/lean4:v4.32.1',
            'mathlib_rev': '520045ab14e26149ee970e2e617ca04b09bde5d6',
            'roots': ['A'],
            'modules': {'A': {**pin(self.root / 'src/A.lean', self.root), 'imports': ['Init']}},
            'data': [pin(self.root / 'src/payload.cnf', self.root)],
            'files': [pin(self.root / name, self.root) for name in sorted(source.CONTROL_FILES)],
            'topological_order': ['A'], 'external_imports': ['Init'],
        }

    def check(self, modules=1, data=1):
        (self.root / 'SOURCE_MANIFEST.json').write_text(json.dumps(self.manifest))
        return source.inspect_package(self.root, module_count=modules, data_count=data, roots=('A',))

    def change_source(self, text, imports=None):
        (self.root / 'src/A.lean').write_text(text)
        self.manifest['modules']['A'].update(pin(self.root / 'src/A.lean', self.root))
        if imports is not None:
            self.manifest['modules']['A']['imports'] = imports

    def test_valid_full_static_controls_do_not_create_build_output(self):
        self.assertEqual(self.check()['proof_modules'], 1)
        self.assertFalse((self.root / '.build').exists())

    def test_hash_drift_rejected(self):
        (self.root / 'src/A.lean').write_text('def changed := 1\n')
        with self.assertRaises(ValueError): self.check()

    def test_extra_source_and_missing_data_rejected(self):
        (self.root / 'src/Extra.lean').write_text('def x := 1\n')
        with self.assertRaises(ValueError): self.check()
        (self.root / 'src/Extra.lean').unlink()
        (self.root / 'src/payload.cnf').unlink()
        with self.assertRaises(ValueError): self.check()

    def test_legacy_lean_outside_src_rejected(self):
        (self.root / 'Check.lean').write_text('import A\n')
        with self.assertRaises(ValueError): self.check()

    def test_reproduction_execution_is_separate_and_src_execution_rejected(self):
        (self.root / 'reproduce').mkdir()
        (self.root / 'reproduce/Emit.lean').write_text('#eval IO.println "export"\n')
        self.assertEqual(self.check()['reproduction_lean_sources_not_proof_scanned'], ['reproduce/Emit.lean'])
        self.change_source('import Init\n#eval IO.println "unexpected"\n')
        with self.assertRaises(ValueError): self.check()

    def test_unreachable_module_rejected(self):
        (self.root / 'src/B.lean').write_text('import Init\ndef b := 1\n')
        self.manifest['modules']['B'] = {**pin(self.root / 'src/B.lean', self.root), 'imports': ['Init']}
        self.manifest['topological_order'].append('B')
        with self.assertRaises(ValueError): self.check(modules=2)

    def test_undeclared_import_rejected(self):
        self.change_source('import Init Std\ndef payload := include_str "payload.cnf"\n')
        with self.assertRaises(RuntimeError): self.check()

    def test_project_import_cannot_masquerade_as_external(self):
        self.change_source('import MissingProject\ndef payload := include_str "payload.cnf"\n', ['MissingProject'])
        self.manifest['external_imports'] = ['MissingProject']
        with self.assertRaises(ValueError): self.check()

    def test_cycle_rejected(self):
        self.change_source('import A\ndef payload := include_str "payload.cnf"\n', ['A'])
        self.manifest['external_imports'] = []
        with self.assertRaises(RuntimeError): self.check()

    def test_unpinned_include_rejected(self):
        self.change_source('import Init\ndef payload := include_str "missing.cnf"\n')
        with self.assertRaises(RuntimeError): self.check()

    def test_wrong_root_count_path_and_symlink_rejected(self):
        original = copy.deepcopy(self.manifest)
        self.manifest['roots'] = ['Other']
        with self.assertRaises(ValueError): self.check()
        self.manifest = copy.deepcopy(original)
        with self.assertRaises(ValueError): self.check(modules=2)
        self.manifest['data'][0]['path'] = '../payload.cnf'
        with self.assertRaises(ValueError): self.check()
        self.manifest = original
        (self.root / 'src/link').symlink_to(self.root / 'src/A.lean')
        with self.assertRaises(ValueError): self.check()

    def test_topological_and_external_censuses_rejected(self):
        self.manifest['topological_order'] = []
        with self.assertRaises(ValueError): self.check()
        self.manifest['topological_order'] = ['A']
        self.manifest['external_imports'] = []
        with self.assertRaises(ValueError): self.check()


class AxiomAndReceiptControls(unittest.TestCase):
    def test_valid_multiline_report(self):
        self.assertEqual(set(validate_report(report())), THEOREMS)

    def test_missing_duplicate_extra_and_bad_axioms_rejected(self):
        examples = ['', report() + '\n' + report(), report().replace('Quot.sound', 'sorryAx', 1),
                    report() + "\n'Unexpected.theorem' does not depend on any axioms"]
        for text in examples:
            with self.assertRaises(ValueError): validate_report(text)

    def test_heavy_small_target_dependency_rejected_before_build(self):
        modules = {name: {'imports': []} for name in MODULES}
        modules[TARGET]['imports'] = sorted(MODULES - {TARGET})
        check_small_closure({'modules': modules})
        modules['ExtraHeavy'] = {'imports': []}
        modules[TARGET]['imports'].append('ExtraHeavy')
        with self.assertRaises(ValueError): check_small_closure({'modules': modules})

    def test_receipt_join_and_binary_exclusion(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            run, artifacts = root / 'run', root / 'artifacts'
            run.mkdir(); artifacts.mkdir()
            manifest = {'modules': {name: {'sha256': 'test-source'} for name in MODULES}}
            (root / 'SOURCE_MANIFEST.json').write_text(json.dumps(manifest))
            digest = hashlib.sha256((root / 'SOURCE_MANIFEST.json').read_bytes()).hexdigest()
            result = {'status': 'PASS', 'targets': [TARGET], 'selected_modules': 5,
                      'completed': sorted(MODULES), 'jobs': 1, 'certificate_command_modules': [],
                      'new_solver_calls': 0, 'baseline_project_artifacts_reused': False,
                      'manifest_sha256': digest}
            (run / 'BUILD_RESULT.json').write_text(json.dumps(result))
            for module in MODULES:
                directory = run / 'modules' / module
                directory.mkdir(parents=True)
                (directory / 'lean.log').write_text(report() if module == TARGET else '')
                (directory / 'output.olean').write_bytes(b'not-an-upload')
                receipt = {'module': module, 'status': 'PASS', 'exit_code': 0,
                           'source': manifest['modules'][module],
                           'log_sha256': hashlib.sha256((directory / 'lean.log').read_bytes()).hexdigest()}
                (directory / 'receipt.json').write_text(json.dumps(receipt))
            self.assertFalse(audit_run(root, run, digest)['complete_theorem_rebuilt'])
            copy_receipts(run, artifacts)
            self.assertFalse(list(artifacts.rglob('*.olean')))
            self.assertEqual(len(list(artifacts.rglob('receipt.json'))), 5)
            (run / 'modules' / TARGET / 'lean.log').write_text('tampered')
            with self.assertRaises(ValueError): audit_run(root, run, digest)
            result['completed'].pop()
            (run / 'BUILD_RESULT.json').write_text(json.dumps(result))
            with self.assertRaises(ValueError): audit_run(root, run, digest)


if __name__ == '__main__':
    unittest.main()
