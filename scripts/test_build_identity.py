"""Reject proof or manifest changes hidden behind documentation substitutions."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_lean_sources as target


class BuildIdentityTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix='ramsey61-build-identity-')
        self.addCleanup(tmp.cleanup)
        self.formal = Path(tmp.name)
        self.identity = json.loads((target.FORMAL/'BUILD_IDENTITY.json').read_bytes())
        self.manifest = json.loads((target.FORMAL/'SOURCE_MANIFEST.json').read_bytes())
        self.accepted = target.read_accepted_manifest_pin()
        for entry in self.identity['modules']:
            path = self.manifest['modules'][entry['module']]['path']
            p=self.formal/path;p.parent.mkdir(parents=True,exist_ok=True)
            p.write_bytes((target.FORMAL/path).read_bytes())
        (self.formal/'BUILD_IDENTITY.json').write_bytes((target.FORMAL/'BUILD_IDENTITY.json').read_bytes())
        self.save_manifest()
        self.entry = self.identity['modules'][0]
        self.row = self.manifest['modules'][self.entry['module']]
        self.source = self.formal/self.row['path']

    def save_manifest(self):
        (self.formal/'SOURCE_MANIFEST.json').write_text(json.dumps(self.manifest,indent=2)+'\n')

    def check(self):
        return target.require_accepted_package(self.formal,
            target.sha((self.formal/'SOURCE_MANIFEST.json').read_bytes()),self.accepted)

    def repin_identity(self):
        raw=(json.dumps(self.identity,indent=2)+'\n').encode()
        (self.formal/'BUILD_IDENTITY.json').write_bytes(raw)
        return patch.object(target,'BUILD_IDENTITY_SHA',target.sha(raw))

    def test_exact_source_identity(self):
        result=self.check()
        self.assertIs(result['complete_theorem_rebuilt'],False)
        self.assertEqual(result['baseline_manifest_sha256'],self.accepted)

    def test_original_manifest(self):
        for entry in self.identity['modules']:
            row=self.manifest['modules'][entry['module']];p=self.formal/row['path'];text=p.read_text()
            for comment in reversed(entry['comments']):text=text.replace(comment['after'],comment['before'],1)
            raw=text.encode();p.write_bytes(raw);row.update(sha256=target.sha(raw),bytes=len(raw))
        self.save_manifest()
        self.assertEqual(self.check()['kind'],'exact_accepted_build')

    def test_code_change_even_with_updated_manifest(self):
        b=self.source.read_bytes()+b'\ndef unapproved : Nat := 42\n';self.source.write_bytes(b)
        self.row.update(sha256=target.sha(b),bytes=len(b));self.save_manifest()
        with self.assertRaisesRegex(ValueError,'Proof source differs'):self.check()

    def test_unrelated_manifest_change(self):
        self.manifest['toolchain']='unapproved';self.save_manifest()
        with self.assertRaisesRegex(ValueError,'not the accepted full-build manifest'):self.check()

    def test_unrelated_module_change(self):
        name=next(m for m in self.manifest['modules'] if m not in target.IDENTITY_MODULES)
        self.manifest['modules'][name]['sha256']='0'*64;self.save_manifest()
        with self.assertRaisesRegex(ValueError,'not the accepted full-build manifest'):self.check()

    def test_unapproved_documentation_change(self):
        b=self.source.read_bytes()+b'\n/-- Extra. -/\n';self.source.write_bytes(b)
        self.row.update(sha256=target.sha(b),bytes=len(b));self.save_manifest()
        with self.assertRaisesRegex(ValueError,'Proof source differs'):self.check()

    def test_identity_digest(self):
        p=self.formal/'BUILD_IDENTITY.json';p.write_bytes(p.read_bytes()+b'\n')
        with self.assertRaisesRegex(ValueError,'Source hash mismatch'):self.check()

    def test_duplicate_module(self):
        self.identity['modules'][1]=copy.deepcopy(self.entry)
        with self.repin_identity(),self.assertRaisesRegex(ValueError,'module census'):self.check()

    def test_missing_span(self):
        self.entry['comments'].pop()
        with self.repin_identity(),self.assertRaisesRegex(ValueError,'span census'):self.check()

    def test_forged_baseline(self):
        self.identity['baseline_manifest_sha256']='0'*64
        with self.repin_identity(),self.assertRaisesRegex(ValueError,'not the accepted full-build manifest'):self.check()

    def test_forged_original_hash(self):
        self.entry['original_source_sha256']='0'*64
        with self.repin_identity(),self.assertRaisesRegex(ValueError,'Proof source differs'):self.check()

    def test_comment_escape(self):
        for bad in ['/-- valid -/\ndef evil := 1','/-- nested /- x -/ -/','/-- unclosed']:
            with self.subTest(bad=bad):
                self.entry['comments'][0]['before']=bad
                with self.repin_identity(),self.assertRaisesRegex(ValueError,'closed documentation comment'):self.check()

    def test_nonunique_span(self):
        self.entry['comments'][0]['after']='/-- nonexistent -/'
        with self.repin_identity(),self.assertRaisesRegex(ValueError,'span is not unique'):self.check()

    def test_duplicate_json_key(self):
        p=self.formal/'BUILD_IDENTITY.json';raw=p.read_bytes().rstrip()[:-1]+b',"modules":[]}\n';p.write_bytes(raw)
        with patch.object(target,'BUILD_IDENTITY_SHA',target.sha(raw)),self.assertRaisesRegex(ValueError,'Duplicate JSON key'):self.check()

    def test_source_symlink(self):
        p=self.formal/'linked';p.write_bytes(self.source.read_bytes());self.source.unlink();self.source.symlink_to(p)
        with self.assertRaisesRegex(ValueError,'Missing/symlink'):self.check()


if __name__=='__main__':unittest.main(verbosity=2)
