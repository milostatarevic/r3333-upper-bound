"""Small release-boundary controls; no archives, Lean builds or solver calls."""
from copy import deepcopy
from pathlib import Path
import json
import tempfile
import unittest
from unittest.mock import patch

import uniform_release as release


class TemporaryFiles(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value if isinstance(value, str) else json.dumps(value))
        return path


class FileCustodyTests(TemporaryFiles):
    def test_watched_source_is_not_archived_but_stays_pinned(self):
        source = self.write('source.lean', 'original')
        files = release.Files()
        files.watch(source)
        files.unchanged()
        self.assertEqual(files.entries, {})
        source.write_text('changed')
        with self.assertRaisesRegex(ValueError, 'Evidence changed'):
            files.unchanged()

    def test_retained_member_cannot_change(self):
        source = self.write('record.json', '{}')
        files = release.Files()
        files.add(source, 'math/record.json')
        source.write_text('{"changed": true}')
        with self.assertRaisesRegex(ValueError, 'Evidence changed'):
            files.unchanged()

    def test_expected_pin_is_required(self):
        source = self.write('source', 'value')
        wrong = {'bytes': 5, 'sha256': '0' * 64}
        for method, args in (('watch', (source, wrong)),
                             ('add', (source, 'source', wrong))):
            with self.subTest(method=method), self.assertRaises(ValueError):
                getattr(release.Files(), method)(*args)

    def test_archive_member_cannot_escape_or_replace_another_source(self):
        source = self.write('one', 'one')
        other = self.write('two', 'two')
        for member in ('../escape', '/absolute', 'a/../../escape'):
            with self.subTest(member=member), self.assertRaises(ValueError):
                release.Files().add(source, member)
        files = release.Files()
        files.add(source, 'one')
        with self.assertRaisesRegex(ValueError, 'Duplicate release member'):
            files.add(other, 'one')

    def test_recorded_path_must_stay_inside_its_origin(self):
        origin = Path('/accepted/build')
        self.assertEqual(release.relative_record(
            {'path': '/accepted/build/modules/test/receipt.json'}, origin),
            Path('modules/test/receipt.json'))
        for path in ('/outside/receipt.json', '/accepted/build/../receipt.json'):
            with self.subTest(path=path), self.assertRaises(ValueError):
                release.relative_record({'path': path}, origin)


class BindingToolTests(TemporaryFiles):
    def setUp(self):
        super().setUp()
        self.formal = self.root / 'formal'
        self.origin = Path('/accepted/formal')
        self.records = []
        for relative in sorted(release.BINDING_TOOLS):
            path = self.write('formal/' + relative, relative)
            self.records.append({'path': str(self.origin / relative),
                                 **release.native.pin(path)})

    def check(self, records):
        files = release.Files()
        release.binding_tools(self.formal, self.origin, records, files)
        return files

    def test_exact_current_tools_are_watched_and_retained(self):
        files = self.check(self.records)
        files.unchanged()
        self.assertEqual(len(files.entries), 11)
        self.assertEqual(len(files.watched), 11)

    def test_wrong_path_with_same_basename_is_rejected(self):
        rows = deepcopy(self.records)
        rows[0]['path'] = str(self.origin / 'other' / Path(rows[0]['path']).name)
        with self.assertRaisesRegex(ValueError, 'exact current set'):
            self.check(rows)

    def test_duplicate_or_missing_driver_is_rejected(self):
        variants = [self.records + [self.records[0]],
                    [r for r in self.records if not r['path'].endswith('/run_binding.py')]]
        for rows in variants:
            with self.subTest(count=len(rows)), self.assertRaisesRegex(ValueError, 'exact current set'):
                self.check(rows)

    def test_noncanonical_alias_is_rejected(self):
        rows = deepcopy(self.records)
        rows[0]['path'] = rows[0]['path'].replace('/uniform/', '/uniform/./')
        with self.assertRaisesRegex(ValueError, 'Noncanonical'):
            self.check(rows)

    def test_driver_change_after_validation_is_rejected(self):
        files = self.check(self.records)
        (self.formal / 'reproduce/uniform/run_binding.py').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'Evidence changed'):
            files.unchanged()


class CurrentInputCustodyTests(TemporaryFiles):
    def setUp(self):
        super().setUp()
        self.tools = self.root/'reproduce'
        archive_pin = {'path':'evidence/D/UUT/full_inputs_000/MANIFEST.json',
                       'bytes':1,'sha256':'1'*64}
        self.old = {'sources': {'A':{'path':'archive-A','bytes':1,'sha256':'a'*64},
                               'C':{'path':'archive-C','bytes':1,'sha256':'c'*64},
                               'D_UU':archive_pin}}
        table = {'schema':'UNIFORM_K61_MARKED_UU_DATA_1','provenance':{
            'source_archive_sha256':release.native.ARCHIVE_SHA,
            'source_manifest':archive_pin}}
        local = {}
        for family,name in release.GENERATOR_DATA.items():
            path = self.write('reproduce/data/'+name, table if family=='D_UU' else '{}')
            local[family] = {'path':'reproduce/data/'+name, **release.native.pin(path)}
        self.new = {'sources':dict(self.old['sources'],C=local['C'],BALANCE=local['BALANCE'])}
        generator = self.write('reproduce/uniform_k61.py','current constructor')
        deps = {name:release.native.pin(self.write('reproduce/'+name,name))
                for name in release.GENERATOR_DEPENDENCIES}
        self.current = {'sources':dict(self.new['sources'],D_UU=local['D_UU']),
                        'generator':release.native.pin(generator),'generator_dependencies':deps}

    def check(self, current=None):
        files = release.Files()
        release.current_input_sources(current or self.current,self.old,self.new,self.current,files,self.tools)
        return files

    def test_current_constructor_and_flat_data_are_independently_pinned(self):
        files = self.check()
        self.assertEqual(len(files.entries),6)
        self.assertEqual(len(files.watched),6)
        files.unchanged()
        # Relocation redirects retained members to archive copies; the current
        # implementation must remain pinned separately through that operation.
        files.entries.clear()
        (self.tools/'data/marked_uu.json').write_text('substitution')
        with self.assertRaisesRegex(ValueError,'Evidence changed'):
            files.unchanged()

    def test_missing_extra_or_substituted_source_is_rejected(self):
        for family in ('A','C','D_UU','BALANCE'):
            for action in ('missing','substituted'):
                current = deepcopy(self.current)
                if action=='missing':
                    del current['sources'][family]
                else:
                    current['sources'][family]['sha256'] = '0'*64
                with self.subTest(family=family,action=action), self.assertRaises(ValueError):
                    self.check(current)
        current = deepcopy(self.current)
        current['sources']['EXTRA'] = current['sources']['A']
        with self.assertRaisesRegex(ValueError,'source census'):
            self.check(current)

    def test_generator_or_dependency_change_is_rejected(self):
        current = deepcopy(self.current)
        current['generator']['sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError,'Watched file mismatch'):
            self.check(current)
        current = deepcopy(self.current)
        current['generator_dependencies']['extra.py'] = current['generator']
        with self.assertRaisesRegex(ValueError,'dependency census'):
            self.check(current)

    def test_changed_table_provenance_is_rejected_even_if_table_pin_is_updated(self):
        path = self.tools/'data/marked_uu.json'
        table = json.loads(path.read_text())
        table['provenance']['source_archive_sha256'] = '0'*64
        path.write_text(json.dumps(table))
        current = deepcopy(self.current)
        current['sources']['D_UU'].update(release.native.pin(path))
        with self.assertRaisesRegex(ValueError,'source provenance'):
            self.check(current)

    def test_binding_table_must_match_exact_input_manifest_and_stay_pinned(self):
        self.write('inputs/MANIFEST.json',self.current)
        table = self.tools/'data/marked_uu.json'
        record = dict(release.native.pin(table),path=str(table))
        with patch.object(release,'__file__',str(self.tools/'uniform_release.py')):
            files = release.Files()
            release.binding_data([record],self.root/'inputs',files)
            for records in ([],[record,record],[dict(record,sha256='0'*64)],
                            [dict(record,path='relative/marked_uu.json')]):
                with self.subTest(records=records), self.assertRaises(ValueError):
                    release.binding_data(records,self.root/'inputs',release.Files())
            table.write_text('changed')
            with self.assertRaisesRegex(ValueError,'Evidence changed'):
                files.unchanged()


def synthetic_case(index, family, number):
    """Identity-only fixture, not a generated formula or native record."""
    row = {'id': index, 'family': family, 'case_id': f'{family}_{number}',
           'formula': {'sha256': f'{index:064x}', 'bytes': 1,
                       'variables': 13656 if family == 'BALANCE' else 7320,
                       'clauses': 524462 if family == 'BALANCE' else 156771}}
    if family == 'BALANCE':
        row['file'] = f'balanced/{number}.cnf'
    else:
        row['units'] = [index + 1, -(index + 2)]
    return row


class CaseMappingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.current = []
        for family, count in release.COUNTS.items():
            for number in range(count):
                cls.current.append(synthetic_case(len(cls.current), family, number))
        cls.catalogs = {
            'abd': cls.current[:release.ABD_CASES] + [
                synthetic_case(release.ABD_CASES+n,'C',n) for n in range(456)],
            'c': [dict(row,id=n,current_index=row['id'])
                  for n,row in enumerate(cls.current[release.ABD_CASES:])],
            'balance': [dict(row,id=n,current_index=row['id'])
                        for n,row in enumerate(cls.current[-3:])]}
        # Unselected source formulas cannot establish current acceptance.
        for row in cls.catalogs['c'][-3:]:
            row['formula'] = dict(row['formula'],sha256='f'*64)
        cls.sources = {g:release.selected_source_rows(rows,g) for g,rows in cls.catalogs.items()}

    def test_complete_mapping_selects_only_current_family_sources(self):
        counts = {'abd':0,'c':0,'balance':0}
        for row in self.current:
            group, source = release.select_source(row,self.sources)
            counts[group] += 1
            self.assertEqual(release.row_identity(row),release.row_identity(source))
            if row['family']=='BALANCE':
                self.assertEqual(group,'balance')
                self.assertLess(source['id'],3)
        self.assertEqual(counts,{'abd':56374,'c':346,'balance':3})
        self.assertEqual(len(self.current),56723)
        self.assertEqual(2*len(self.current),113446)

    def test_changed_units_case_or_formula_is_rejected(self):
        for index,field,replacement in ((0,'units',[-1,-2]),(56374,'units',[1,2]),
                (56374,'case_id','wrong'),(56374,'id',56375),(0,'family','C'),
                (56720,'file','balanced/substitute.cnf')):
            row=deepcopy(self.current[index]);row[field]=replacement
            with self.subTest(index=index,field=field),self.assertRaises(ValueError):
                release.select_source(row,self.sources)
        row=deepcopy(self.current[56720]);row['formula']['variables']=7320
        with self.assertRaisesRegex(ValueError,'formula mismatch'):
            release.select_source(row,self.sources)

    def test_wrong_source_local_or_global_index_is_rejected(self):
        for group in ('abd','c','balance'):
            rows=list(self.catalogs[group]);rows[0]=dict(rows[0],id=-1)
            with self.subTest(group=group),self.assertRaisesRegex(ValueError,'local index'):
                release.selected_source_rows(rows,group)
        for group,index in (('c',56374),('balance',56720)):
            sources={g:list(rows) for g,rows in self.sources.items()}
            sources[group][0]=dict(sources[group][0],current_index=-1)
            with self.subTest(group=group),self.assertRaisesRegex(ValueError,'mapping changed'):
                release.select_source(self.current[index],sources)

    def test_missing_duplicate_or_wrong_selected_boundary_is_rejected(self):
        for group in ('abd','c','balance'):
            rows=self.catalogs[group]
            for altered in (rows[1:],rows+[rows[0]]):
                with self.subTest(group=group),self.assertRaises(ValueError):
                    release.selected_source_rows(altered,group)
        sources=dict(self.sources,balance=self.catalogs['c'][-3:])
        with self.assertRaisesRegex(ValueError,'formula mismatch'):
            release.select_source(self.current[-3],sources)


class AxiomAuditTests(unittest.TestCase):
    GOOD = ("'UniformK61.WholeProof.ramsey61' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]\n"
            "'UniformK61.WholeProof.native_case_count' does not depend on any axioms\n")

    def test_exact_two_standard_reports(self):
        self.assertEqual(set(release.check_axioms(self.GOOD)), release.AXIOM_NAMES)

    def test_unsealed_missing_duplicate_or_extra_report_is_rejected(self):
        for text in (self.GOOD.replace('propext', 'sorryAx'),
                     self.GOOD.replace('propext', 'propext, propext'),
                     self.GOOD.splitlines()[0],
                     self.GOOD + self.GOOD.splitlines()[0] + '\n',
                     self.GOOD + 'unexpected output\n'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                release.check_axioms(text)


class MathematicalAcceptanceTests(TemporaryFiles):
    def setUp(self):
        super().setUp()
        self.formal = self.root / 'formal'
        source = self.write('formal/src/UniformK61/WholeProof.lean', '-- fixture\n')
        module = {'path': 'src/UniformK61/WholeProof.lean',
                  **release.native.pin(source), 'imports': []}
        manifest = {'modules': {'UniformK61.WholeProof': module},
                    'roots': ['UniformK61.WholeProof'], 'data': [], 'files': []}
        self.manifest = self.write('formal/SOURCE_MANIFEST.json', manifest)
        self.build = self.root / 'build'
        self.binding = self.root / 'binding'
        self.good_build = {'status': 'PASS', 'baseline_project_artifacts_reused': False,
                           'new_solver_calls': 0, 'failures': {}, 'pending': [],
                           'interrupted': False,
                           'manifest_sha256': release.native.pin(self.manifest)['sha256'],
                           'selected_modules': 1, 'completed': ['UniformK61.WholeProof'],
                           'targets': ['UniformK61.WholeProof']}
        self.write('build/BUILD_RESULT.json', self.good_build)
        self.write('binding/RUN_RESULT.json', {})

    def inspect(self):
        # These fixtures fail before any compiler/library inspection or import.
        return release.inspect_math(self.formal, self.manifest, self.build,
                                    self.binding, self.root / 'inputs', release.Files())

    def test_running_reused_failed_interrupted_or_wrong_manifest_build_is_rejected(self):
        for change in ({'status': 'RUNNING'}, {'baseline_project_artifacts_reused': True},
                       {'failures': {'module': 'failed'}}, {'pending': ['module']},
                       {'interrupted': True}, {'new_solver_calls': 1},
                       {'manifest_sha256': '0' * 64}):
            self.write('build/BUILD_RESULT.json', dict(self.good_build, **change))
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'fresh source-only'):
                self.inspect()

    def test_incomplete_source_closure_is_rejected(self):
        for change in ({'completed': []}, {'selected_modules': 2}, {'targets': []}):
            self.write('build/BUILD_RESULT.json', dict(self.good_build, **change))
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'source closure'):
                self.inspect()

    def test_extra_or_changed_source_is_rejected(self):
        extra = self.write('formal/src/Extra.lean', '-- not manifested\n')
        with self.assertRaisesRegex(ValueError, 'source census differs'):
            self.inspect()
        extra.unlink()
        self.write('formal/src/UniformK61/WholeProof.lean', '-- changed\n')
        with self.assertRaisesRegex(ValueError, 'source/data pin mismatch'):
            self.inspect()

    def test_wrong_or_incomplete_binding_is_rejected(self):
        good = {'schema': 'UNIFORM_K61_FRESH_BUILD_BINDING_1', 'status': 'PASS',
                'cases': 56723, 'new_solver_calls': 0}
        for change in ({'cases': 56830}, {'cases': 349}, {'status': 'RUNNING'},
                       {'error': 'emission failed'}, {'new_solver_calls': 1}):
            self.write('binding/RUN_RESULT.json', dict(good, **change))
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'fresh binding required'):
                self.inspect()


class NativeAcceptanceTests(TemporaryFiles):
    def setUp(self):
        super().setUp()
        self.rows=[{'id':0,'family':'C','case_id':'case'}]
        self.campaign={'family_counts':{'C':1}}
        self.terminal={'state':'COMPLETE','completed':2,'total':2,'statuses':{'UNSAT':2},
            'active':[],'retained_inputs_and_tools_unchanged':True,
            'families':{'C':{'UNSAT':2}},'native_CPU_seconds':3.0}
        self.events=[{'id':0,'family':'C','case_id':'case','solver':solver,'status':'UNSAT',
            'native_CPU_seconds':cpu,'result':f'runs/{solver}/00000/RESULT.json'}
            for solver,cpu in [('kissat',1.0),('cadical',2.0)]]
        self.save()

    def save(self):
        self.write('TERMINAL.json',self.terminal);self.write('STATUS.json',self.terminal)
        self.write('EVENTS.jsonl',''.join(json.dumps(row)+'\n' for row in self.events))

    def check(self):
        return release.source_ledger(self.root,self.rows,self.campaign)

    def test_complete_source_ledger_preserves_original_local_ids(self):
        self.assertEqual(set(self.check()),{('kissat',0),('cadical',0)})

    def test_partial_faulted_or_non_unsat_source_is_rejected(self):
        good=deepcopy(self.terminal)
        for change in ({'state':'RUNNING'},{'completed':1},{'active':[{}]},
                       {'retained_inputs_and_tools_unchanged':False},
                       {'statuses':{'SAT':1,'UNSAT':1}},{'native_CPU_seconds':4.0},
                       {'families':{'C':{'UNSAT':1}}}):
            self.terminal=dict(good,**change);self.save()
            with self.subTest(change=change),self.assertRaises(ValueError):self.check()
        self.terminal=good
        for verdict in ('SAT','UNKNOWN','ERROR'):
            self.events[0]['status']=verdict;self.save()
            with self.subTest(verdict=verdict),self.assertRaises(ValueError):self.check()

    def test_missing_duplicate_or_misbound_event_is_rejected(self):
        good=deepcopy(self.events)
        for events in (good[:1],good+[good[0]],
                       [dict(good[0],id=1),good[1]],
                       [dict(good[0],case_id='other'),good[1]],
                       [dict(good[0],result='runs/kissat/00001/RESULT.json'),good[1]],
                       [dict(good[0],native_CPU_seconds=float('nan')),good[1]]):
            self.events=events;self.save()
            with self.subTest(events=events),self.assertRaises(ValueError):self.check()

    def test_selected_catalog_never_reads_unselected_formula_payload(self):
        import gzip
        inputs=self.root/'inputs';inputs.mkdir()
        marked=synthetic_case(0,'C',0);marked['units']=[1]
        import hashlib
        body=b'1 0\n';raw=b'p cnf 7320 156771\n'+body+b'1 0\n'
        marked['formula']={'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),
                           'variables':7320,'clauses':156771}
        ignored=synthetic_case(1,'BALANCE',0)
        path=inputs/'cases.jsonl.gz'
        with gzip.open(path,'wt') as stream:
            for row in (marked,ignored):stream.write(json.dumps(row)+'\n')
        counts={'C':1,'BALANCE':1}
        self.assertEqual(len(release.native.read_catalog(path,body,counts,{'C'})),2)
        with self.assertRaises((ValueError,FileNotFoundError)):
            release.native.read_catalog(path,body,counts)
        marked['formula']['sha256']='0'*64
        with gzip.open(path,'wt') as stream:
            for row in (marked,ignored):stream.write(json.dumps(row)+'\n')
        with self.assertRaisesRegex(ValueError,'Incorrect formula pin'):
            release.native.read_catalog(path,body,counts,{'C'})


class PackageGateTests(TemporaryFiles):
    def release_record(self):
        return {'schema': 'UNIFORM_K61_CURRENT_RELEASE_1', 'cases': 56723,
                'native_runs': 113446, 'family_counts': release.COUNTS,
                'native': {'status': 'PASS_NATIVE_CURRENT_56723'},
                'mathematics': {'cases': 56723, 'live_build_custody_rechecked': True}}

    def reject_without_creating_archive(self, record, message):
        target = self.root / 'must-not-exist.tar.gz'
        with self.assertRaisesRegex(ValueError, message):
            release.package(target, release.Files(), record)
        self.assertFalse(target.exists())

    def test_native_acceptance_alone_is_not_release_acceptance(self):
        record = self.release_record()
        record['mathematics']['live_build_custody_rechecked'] = False
        self.reject_without_creating_archive(record, 'fresh mathematical acceptance')

    def test_current_math_does_not_accept_partial_or_wrong_native_boundary(self):
        for change in ({'cases': 349}, {'cases': 56830}, {'native_runs': 698},
                       {'native': {'status': 'INCOMPLETE'}},
                       {'native': {'status': 'SAT'}}, {'native': {'status': 'UNKNOWN'}},
                       {'family_counts': {'C':346,'BALANCE':3}}):
            with self.subTest(change=change):
                self.reject_without_creating_archive(dict(self.release_record(), **change),
                                                     'fresh mathematical acceptance')

    def test_summary_without_raw_math_records_cannot_be_packaged(self):
        self.reject_without_creating_archive(self.release_record(), 'Raw mathematical acceptance')


if __name__ == '__main__':
    unittest.main()
