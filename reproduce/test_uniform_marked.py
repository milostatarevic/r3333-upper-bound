"""Controls for physical marked-case data and immutable campaign provenance."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import uniform_k61 as generator
import uniform_verify as verifier


class MarkedDataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data, cls.identity = generator.load_marked_uu()

    def test_flat_index_and_opaque_labels(self):
        rows = self.data['cases']
        self.assertEqual(sorted(r['index'] for r in rows), list(range(679)))
        for row in rows:
            renamed = dict(row, case_id='opaque evidence label')
            for owner in ('UUU','UUT'):
                self.assertEqual(generator.d_units(owner,row), generator.d_units(owner,renamed))

    def test_missing_or_outside_support_rejected(self):
        row = copy.deepcopy(self.data['cases'][0])
        row['support'].pop(0)
        with self.assertRaisesRegex(ValueError,'support shape'):
            generator.d_units('UUU',row)
        row = copy.deepcopy(self.data['cases'][0])
        row['support'][-1] = 47
        with self.assertRaisesRegex(ValueError,'support shape'):
            generator.d_units('UUU',row)

    def test_cross_edge_and_color_changes_rejected(self):
        for change in ('missing','wrong_endpoints','forbidden_color'):
            row = copy.deepcopy(self.data['cases'][0])
            if change == 'missing': row['cross_edges'].pop()
            elif change == 'wrong_endpoints': row['cross_edges'][0][:2] = [33,47]
            else: row['cross_edges'][0][2] = 3
            with self.assertRaisesRegex(ValueError,'cross-support facts'):
                generator.d_units('UUU',row)

    def test_all_nonroot_membership_is_explicit(self):
        for row in self.data['cases']:
            units = generator.d_units('UUU',row)
            for v, literal in enumerate(units[-59:],1):
                self.assertEqual(abs(literal),generator.edge(61,v,60,3))
                self.assertEqual(literal>0,v in row['support'])

    def test_changed_source_data_rejected_before_construction(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp)/'marked_uu.json'
            path.write_bytes(generator.MARKED_UU_DATA.read_bytes()+b' ')
            with patch.object(generator,'MARKED_UU_DATA',path):
                with self.assertRaisesRegex(ValueError,'finite-data identity'):
                    generator.load_marked_uu()


class MarkedBindingIndexTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[1]/'formal/reproduce/uniform/check_marked_uu.py'
        spec = importlib.util.spec_from_file_location('marked_binding_control',path)
        cls.checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.checker)
        cls.data, cls.identity = generator.load_marked_uu()

    def test_explicit_indices_do_not_assume_catalog_order(self):
        manifest = {'sources':{'D_UU':self.identity}}
        indices,_ = self.checker.case_indices(generator.MARKED_UU_DATA,manifest)
        self.assertEqual(len(indices),679)
        self.assertNotEqual([r['index'] for r in self.data['cases']],list(range(679)))
        for row in self.data['cases']:
            self.assertEqual(indices[row['case_id']],row['index'])

    def test_duplicate_index_rejected_even_with_matching_file_pin(self):
        data = copy.deepcopy(self.data)
        data['cases'][1]['index'] = data['cases'][0]['index']
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp)/'marked_uu.json'
            raw = json.dumps(data).encode();path.write_bytes(raw)
            identity = {'path':'reproduce/data/marked_uu.json','bytes':len(raw),
                        'sha256':hashlib.sha256(raw).hexdigest()}
            with self.assertRaisesRegex(ValueError,'bijection'):
                self.checker.case_indices(path,{'sources':{'D_UU':identity}})


class CampaignDataCustodyTests(unittest.TestCase):
    def fixture(self, normalized):
        root = Path('/retained-campaign')
        p = {'bytes':1,'sha256':'a'*64}
        manifest = {'catalog':p,'base':p,'generator':p,
                    'generator_dependencies':{'uniform_c.py':p,'uniform_balance.py':p},
                    'sources':{'C':p,'BALANCE':p,'D_UU':dict(p,path=(
                        'reproduce/data/marked_uu.json' if normalized else
                        'evidence/D/UUT/full_inputs_000/MANIFEST.json'))}}
        campaign = {'catalog':p,'base':p,'generator':p,'runner':p,'input_manifest':p,
                    'generator_dependencies':manifest['generator_dependencies'],
                    'generator_data':{'c_entrances.json':p,'balance_anchors.json':p},
                    'solvers':{name:{'version':version,'options':[],
                                'path':'/immutable/'+name,'binary':p}
                               for name,version in verifier.SOLVERS.items()}}
        if normalized: campaign['generator_data']['marked_uu.json']=p
        return root,manifest,campaign,p

    def test_original_and_normalized_campaigns_bind_their_own_data(self):
        for normalized in (False,True):
            root,manifest,campaign,p = self.fixture(normalized)
            with patch.object(verifier,'pin',return_value=p):
                verifier.check_pins(root,campaign,manifest)

    def test_missing_new_data_is_rejected(self):
        root,manifest,campaign,p = self.fixture(True)
        del campaign['generator_data']['marked_uu.json']
        with patch.object(verifier,'pin',return_value=p):
            with self.assertRaisesRegex(ValueError,'data census'):
                verifier.check_pins(root,campaign,manifest)

    def test_old_campaign_cannot_silently_adopt_new_data(self):
        root,manifest,campaign,p = self.fixture(False)
        campaign['generator_data']['marked_uu.json']=p
        with patch.object(verifier,'pin',return_value=p):
            with self.assertRaisesRegex(ValueError,'data census'):
                verifier.check_pins(root,campaign,manifest)


if __name__ == '__main__': unittest.main()
