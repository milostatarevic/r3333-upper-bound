#!/usr/bin/env python3
"""Failure-focused checks for the selected native evidence boundary; no SAT runs."""
import copy
import gzip
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'reproduce'))
import publication_native_evidence as evidence
import publication_cadical_evidence as cadical


class SelectionTests(unittest.TestCase):
    def test_output_cannot_modify_or_recursively_copy_source(self):
        evidence.separate_output(Path('/work/new'),(Path('/work/source'),))
        for output in ('/work/source','/work/source/nested','/work'):
            with self.subTest(output=output),self.assertRaisesRegex(ValueError,'separate'):
                evidence.separate_output(Path(output),(Path('/work/source'),))

    def make_expected(self):
        owners = {'BALANCE_BRACE_15':624,'BALANCE_BRACE_16':96,
                  'C1_ENTRANCE':692,'C2_ENTRANCE':7840,
                  **{'BALANCE_ALL_FIVE_'+o:1 for o in ('UU','UT','TT')}}
        return {owner+'_'+str(i):{'owner':owner,'sha256':'a'*64}
                for owner,n in owners.items() for i in range(n)}

    def test_only_all_braces_replaced(self):
        selected = evidence.selected_legacy(self.make_expected(),'closure')
        self.assertEqual(len(selected),8535)
        self.assertFalse(any('BRACE' in v['owner'] for v in selected.values()))
        self.assertEqual(sum(v['owner'].startswith('BALANCE_ALL_FIVE_') for v in selected.values()),3)

    def test_missing_brace_cannot_silently_change_selection(self):
        rows = self.make_expected(); rows.pop('BALANCE_BRACE_15_0')
        with self.assertRaisesRegex(ValueError,'retired brace boundary'):
            evidence.selected_legacy(rows,'closure')

    def test_missing_all_five_refused(self):
        rows = self.make_expected(); rows.pop('BALANCE_ALL_FIVE_TT_0')
        with self.assertRaisesRegex(ValueError,'selected closure boundary'):
            evidence.selected_legacy(rows,'closure')

    def test_unknown_owner_refused(self):
        rows = self.make_expected(); rows['unexpected'] = {'owner':'UNKNOWN','sha256':'a'*64}
        with self.assertRaisesRegex(ValueError,'selected closure boundary'):
            evidence.selected_legacy(rows,'closure')

    def test_export_rejects_retired_and_unknown_keys(self):
        groups = {'closure':evidence.selected_legacy(self.make_expected(),'closure'),
                  'balance':{'C2_ROOT_UU':{'sha256':'b'*64}}}
        for key in ('closure/BALANCE_BRACE_15_0','balance/C2_ROOT_ZZ','../secret','C2_ROOT_UU'):
            with self.subTest(key=key), self.assertRaises(ValueError):
                evidence.find_selected(groups,key)
        self.assertEqual(evidence.find_selected(groups,'balance/C2_ROOT_UU')[:2],('balance','C2_ROOT_UU'))

    def test_selection_digest_binds_family_id_and_hash(self):
        groups = {k:{} for k in ('e','abd','closure','balance')}
        groups['balance']['C2_ROOT_UU'] = {'sha256':'a'*64}
        original = evidence.selection_digest(groups)
        groups['balance']['C2_ROOT_UU']['sha256'] = 'b'*64
        self.assertNotEqual(original,evidence.selection_digest(groups))
        groups['balance'] = {}; groups['closure']['C2_ROOT_UU'] = {'sha256':'a'*64}
        self.assertNotEqual(original,evidence.selection_digest(groups))


class NativeLogTests(unittest.TestCase):
    def test_one_unsat_required(self):
        evidence.exact_verdict(b'c header\ns UNSATISFIABLE\nc exit 20\n',20,'UNSAT')
        for log,code in ((b's UNSATISFIABLE\ns UNSATISFIABLE\n',20),
                         (b's UNSATISFIABLE\ns SATISFIABLE\n',20),
                         (b'c UNKNOWN\n',20),(b's UNSATISFIABLE\n',0)):
            with self.subTest(log=log,code=code), self.assertRaises(ValueError):
                evidence.exact_verdict(log,code,'UNSAT')

    def test_unresolved_never_unsat(self):
        evidence.exact_verdict(b'c UNKNOWN\n',-14,'TIMEOUT')
        evidence.exact_verdict(b'c interrupted\n',-15,'INTERRUPTED')
        for status in ('TIMEOUT','INTERRUPTED','ERROR','SAT'):
            with self.subTest(status=status), self.assertRaises(ValueError):
                evidence.exact_verdict(b's UNSATISFIABLE\n',20,status)

    def test_cpu_parse_requires_unique_field(self):
        log = b'c process-time: 2s 2.17 seconds\n'
        self.assertEqual(str(evidence.legacy_cpu(log)),'2.17')
        for bad in (b'',log+log,b'c process-time: nan seconds\n'):
            with self.assertRaises(ValueError): evidence.legacy_cpu(bad)


class ExperimentTests(unittest.TestCase):
    def fixture(self):
        origin = '/original/experiment'; solver = '/solver/kissat/4.0.4/bin/kissat'
        inp = {'id':'C2_ROOT_UU','path':'/original/source/C2_ROOT_UU.cnf','sha256':'a'*64}
        jid = 'C2_ROOT_UU_kissat'; raw = b'c native full log\ns UNSATISFIABLE\nc exit 20\n'
        compressed = gzip.compress(raw,mtime=0)
        plan = {'solvers':{'kissat':{'path':solver}},'resume_command':['/python3']}
        row = {'job_id':jid,'input_id':inp['id'],'solver':'kissat',
               'command':[solver,inp['path']],
               'launch_command':['/python3','-B',origin+'/cpu_exec.py','3600','3605',solver,inp['path']],
               'status':'UNSAT','exit_code':20,'limit_reason':None,
               'started_utc':'2026-11-02T00:00:00+00:00','finished_utc':'2026-11-02T00:00:11+00:00',
               'elapsed_seconds':11.0,'native_cpu_seconds':10.0,'user_cpu_seconds':9.0,'sys_cpu_seconds':1.0,
               'log':{'path':origin+'/jobs/'+jid+'/native.log','gzip_path':origin+'/jobs/'+jid+'/native.log.gz',
                      **evidence.pin_bytes(raw),'gzip_sha256':evidence.sha(compressed),'gzip_bytes':len(compressed)}}
        for suffix in ('before','after'):
            row['input_sha256_'+suffix] = inp['sha256']
            row['solver_sha256_'+suffix] = evidence.SOLVERS['kissat'][1]
        return row,raw,compressed,inp,'kissat',jid,plan,origin

    def test_exact_receipt(self):
        result = evidence.experiment_job(*self.fixture())
        self.assertEqual(result['status'],'UNSAT')

    def test_receipt_mismatches(self):
        for field,value in [('status','TIMEOUT'),('exit_code',0),('input_sha256_after','b'*64),
                            ('solver_sha256_before','b'*64),('native_cpu_seconds',12.0),
                            ('limit_reason','cpu'),('command',['/other','input'])]:
            values = list(self.fixture()); values[0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                evidence.experiment_job(*values)

    def test_corrupt_compressed_log(self):
        values = list(self.fixture()); values[2] += b'corrupt'
        with self.assertRaises(ValueError): evidence.experiment_job(*values)

    def test_conflicting_native_verdict(self):
        values = list(self.fixture()); values[1] += b's SATISFIABLE\n'
        with self.assertRaises(ValueError): evidence.experiment_job(*values)


class SnapshotTests(unittest.TestCase):
    def test_filtered_copy_preserves_raw_rows_and_source(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory)/'source.sqlite3'; target = Path(directory)/'selected.sqlite3'
            db = sqlite3.connect(source)
            fields = [f'{name} '+('BLOB' if name=='log_gzip' else '') for name in evidence.historical.COLUMNS]
            db.execute('CREATE TABLE attempts ('+','.join(fields)+')')
            db.execute('CREATE TABLE metadata (key TEXT,value TEXT)')
            db.execute('INSERT INTO metadata VALUES (?,?)',('origin','unchanged'))
            retained = tuple(['keep',1,'C1_ENTRANCE','a'*64,'b'*64,'c'*64,300,'start','end',1.0,20,'UNSAT','[]','d'*64,b'original gzip'])
            placeholders = ','.join('?' for _ in retained)
            db.execute('INSERT INTO attempts VALUES ('+placeholders+')',retained)
            for i in range(720):
                row = list(retained); row[0] = 'brace'+str(i); row[2] = 'BALANCE_BRACE_15' if i<624 else 'BALANCE_BRACE_16'
                db.execute('INSERT INTO attempts VALUES ('+placeholders+')',row)
            db.commit(); db.row_factory=sqlite3.Row
            original_rows=[evidence.bounded_row(dict(r)) for r in db.execute('SELECT * FROM attempts ORDER BY case_id,attempt')]
            original_digest=evidence.sha(b''.join((json.dumps(r,sort_keys=True,separators=(',',':'))+'\n').encode() for r in original_rows))
            db.close(); before = evidence.pin(source)
            ledger=Path(directory)/'provenance/retired-closure-attempts.jsonl'; ledger.parent.mkdir()
            evidence.filtered_snapshot(source,target,{'keep':{}},ledger)
            self.assertEqual(evidence.pin(source),before)
            selected = sqlite3.connect(target)
            self.assertEqual(selected.execute('SELECT * FROM attempts').fetchall(),[retained])
            self.assertEqual(selected.execute('SELECT * FROM metadata').fetchall(),[('origin','unchanged')])
            selected.close()
            class Store:
                def path(self,member): return Path(directory)/member
            parent={'campaigns':{'closure':{'database':'selected.sqlite3'}},
                    'verification':{'closure':{'attempts':721,'ordered_row_and_compressed_log_hash_sha256':original_digest}}}
            expected={r['case_id']:{} for r in original_rows}
            self.assertEqual(evidence.closure_subset_proof(Store(),parent,expected,{'keep':{}})['omitted_attempts'],720)
            altered=sqlite3.connect(target); altered.execute("UPDATE attempts SET started_utc='altered'"); altered.commit(); altered.close()
            with self.assertRaisesRegex(ValueError,'unchanged subset'):
                evidence.closure_subset_proof(Store(),parent,expected,{'keep':{}})


class CaDiCaLPublicationTests(unittest.TestCase):
    def alarm_row(self):
        return {'returncode':-14,'interrupted':0,'timed_out':0,'elapsed_seconds':300.01,'limit_seconds':300}

    def test_complete_native_alarm_is_unresolved(self):
        raw=b'c UNKNOWN\nc exit 0\nc raising signal 14 (SIGALRM)\n'
        self.assertEqual(cadical.effective_status(raw,self.alarm_row()),'TIMEOUT')
        for changed in (raw.replace(b'c exit 0\n',b''),raw.replace(b'c UNKNOWN',b'c other'),raw+b's UNSATISFIABLE\n'):
            self.assertEqual(cadical.effective_status(changed,self.alarm_row()),'ERROR')
        early=self.alarm_row(); early['elapsed_seconds']=12
        self.assertEqual(cadical.effective_status(raw,early),'ERROR')

    def test_interrupted_exit_never_gets_unsat_credit(self):
        row=self.alarm_row(); row.update(returncode=-999,interrupted=1)
        self.assertEqual(cadical.effective_status(b's UNSATISFIABLE\n',row),'INTERRUPTED')
        self.assertEqual(cadical.effective_status(b's SATISFIABLE\n',row),'ERROR')

    def test_history_requires_resolution_and_exact_caps(self):
        cadical.check_history([(1,300,'INTERRUPTED'),(2,300,'TIMEOUT'),(3,1800,'UNSAT')])
        for history in ([(1,300,'TIMEOUT')],[(1,300,'TIMEOUT'),(2,300,'UNSAT')],
                        [(1,300,'UNSAT'),(2,1800,'UNSAT')],[(2,300,'UNSAT')]):
            with self.subTest(history=history),self.assertRaises(ValueError): cadical.check_history(history)

    def complete_report(self):
        return {'passed':True,'completion_claim':True,'requires_attention':False,'total_cases':296797,
                'unique_accepted_unsat_cases':296797,'remaining_cases':0,'active_leases':0,
                'invalid_attempts_or_histories':[],'sat_case_ids':[],'sat_unsat_conflict_ids':[],
                'original_history_unchanged':True,'reviewed_native_timeout_attempts':1,
                'attempts_seen':300000,'attempts_integrity_checked':300000,
                'checker':{'sha256':cadical.CHECKER},'continuation':{'sha256':cadical.CONTINUATION}}

    def test_complete_gate_rejects_partial_sat_errors_or_changed_history(self):
        cadical.completion_gate(self.complete_report())
        for field,value in [('completion_claim',False),('unique_accepted_unsat_cases',296796),
                            ('active_leases',1),('sat_case_ids',['some-case']),('original_history_unchanged',False),
                            ('reviewed_native_timeout_attempts',0),('attempts_integrity_checked',299999),
                            ('attempts_seen',None),('attempts_seen',True)]:
            report=self.complete_report(); report[field]=value
            with self.subTest(field=field),self.assertRaises(ValueError): cadical.completion_gate(report)

    def test_ongoing_campaign_import_refused_before_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory); progress={'controller_status':'RUNNING','unique_unsat_cases':156135,'active':[]}
            (path/'progress.json').write_text(json.dumps(progress))
            with self.assertRaisesRegex(ValueError,'not complete'): cadical.stopped_completion_gate(path)
            self.assertEqual(sorted(p.name for p in path.iterdir()),['progress.json'])

    def test_exact_component_file_set_excludes_extra_jobs(self):
        members=evidence.expected_members({'files':{}})
        self.assertIn('experiment/jobs/C2_ROOT_UU_kissat/result.json',members)
        self.assertNotIn('experiment/jobs/EXTRA_kissat/result.json',members)
        self.assertNotIn('cadical/results.sqlite3',members)
        self.assertEqual(evidence.expected_members({'files':{}},True)-members,cadical.MEMBERS)


if __name__ == '__main__': unittest.main()
