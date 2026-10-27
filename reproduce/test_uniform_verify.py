"""Negative controls for native evidence acceptance and complete-census gating."""
import gzip
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import uniform_verify as verify


def save(path, value):
    path.write_text(json.dumps(value))


def fixture(root, solver='kissat', conflicts=True):
    job=root/'runs'/solver/'00000';job.mkdir(parents=True)
    identity={'path':'/frozen/tools/'+solver,'version':verify.SOLVERS[solver],
              'binary':{'bytes':1,'sha256':'f'*64},'options':[]}
    expected={'id':0,'family':'A','case_id':'case','formula':
              {'bytes':42,'sha256':'a'*64,'variables':7320,'clauses':156771}}
    start={'schema':'UNIFORM_K61_START_1',**expected,'solver':solver,
           'solver_identity':identity,'worker_pid':50,'time_policy':verify.POLICY,
           'started_utc':'2026-10-13T00:00:01+00:00'}
    digest={'bytes':42,'sha256':'a'*64};command=[identity['path'],'/dev/fd/3']
    native={'pid':51,'started_utc':'2026-10-13T00:00:01.100000+00:00',
            'input_before':digest,'command':command}
    log=f'c Version {identity["version"]}\n'
    if conflicts:log+='c conflicts: 12\n'
    log+='s UNSATISFIABLE\nc exit 20\n'
    (job/'solver.log').write_text(log)
    result={**start,'input_before':digest,'input_after':digest,'command':command,
            'status':'UNSAT','exit_code':20,'raw_wait_status':5120,
            'user_CPU_seconds':1.,'system_CPU_seconds':.25,'native_CPU_seconds':1.25,
            'native_wall_seconds':1.8,'job_wall_seconds':2.,'peak_RSS_bytes':1024,
            'completed_utc':'2026-10-13T00:00:03+00:00','log':verify.pin(job/'solver.log'),
            'conflicts':12 if conflicts else None,'conflicts_reported':conflicts}
    save(job/'START.json',start);save(job/'NATIVE_START.json',native);save(job/'RESULT.json',result)
    return job,expected,identity,result


class EvidenceControls(unittest.TestCase):
    def test_selected_family_acceptance_cannot_package_whole_proof(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root/'bad.tar.gz'
            with self.assertRaisesRegex(ValueError, 'complete proof package'):
                verify.pack(root, target, {'status': 'PASS', 'inventory': False,
                                          'complete_proof_census': False})
            self.assertFalse(target.exists())

    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
        self.job,self.row,self.solver,self.result=fixture(self.root)
        self.started=verify.utc_time('2026-10-13T00:00:00+00:00')

    def tearDown(self):self.temp.cleanup()

    def check(self):return verify.check_record(self.job,self.row,'kissat',self.solver,self.started)

    def test_complete_record(self):self.assertEqual(self.check()['status'],'UNSAT')

    def test_changed_log(self):
        with (self.job/'solver.log').open('a') as f:f.write('s SATISFIABLE\n')
        with self.assertRaisesRegex(ValueError,'Log hash'):self.check()
        self.result['log']=verify.pin(self.job/'solver.log');save(self.job/'RESULT.json',self.result)
        with self.assertRaisesRegex(ValueError,'conflicting'):self.check()

    def test_wrong_case_identity(self):
        self.result['case_id']='other';save(self.job/'RESULT.json',self.result)
        with self.assertRaisesRegex(ValueError,'case_id'):self.check()

    def test_after_hash_mismatch(self):
        self.result['input_after']={'bytes':42,'sha256':'b'*64};save(self.job/'RESULT.json',self.result)
        with self.assertRaisesRegex(ValueError,'binding'):self.check()

    def test_unsat_requires_exit20(self):
        self.result['exit_code']=0;save(self.job/'RESULT.json',self.result)
        with self.assertRaisesRegex(ValueError,'successful'):self.check()

    def test_bad_cpu_accounting(self):
        self.result['native_CPU_seconds']=1.5;save(self.job/'RESULT.json',self.result)
        with self.assertRaisesRegex(ValueError,'CPU sum'):self.check()
        self.result['native_CPU_seconds']=float('nan');save(self.job/'RESULT.json',self.result)
        with self.assertRaisesRegex(ValueError,'Invalid native'):self.check()

    def test_printed_cpu_is_bounded_by_whole_process_usage(self):
        log=(self.job/'solver.log').read_text()+'c process-time: 1s 1.00 seconds\n'
        (self.job/'solver.log').write_text(log);self.result['log']=verify.pin(self.job/'solver.log')
        save(self.job/'RESULT.json',self.result);self.check()
        (self.job/'solver.log').write_text(log.replace('1.00 seconds','2.00 seconds'))
        self.result['log']=verify.pin(self.job/'solver.log');save(self.job/'RESULT.json',self.result)
        with self.assertRaisesRegex(ValueError,'Printed CPU'):
            self.check()

    def test_null_conflicts_only_when_unreported(self):
        self.result['conflicts']=None;self.result['conflicts_reported']=False
        save(self.job/'RESULT.json',self.result)
        with self.assertRaisesRegex(ValueError,'flag'):self.check()
        log=(self.job/'solver.log').read_text().replace('c conflicts: 12\n','')
        (self.job/'solver.log').write_text(log);self.result['log']=verify.pin(self.job/'solver.log')
        save(self.job/'RESULT.json',self.result);self.assertIsNone(self.check()['conflicts'])

    def test_options_rejected(self):
        self.result['command'].insert(1,'--unsat')
        save(self.job/'RESULT.json',self.result)
        with self.assertRaisesRegex(ValueError,'command'):self.check()

    def test_symlink_record_rejected(self):
        original=self.job/'RESULT.json';target=self.root/'copy.json'
        target.write_bytes(original.read_bytes());original.unlink();original.symlink_to(target)
        with self.assertRaisesRegex(ValueError,'regular JSON'):self.check()

    def test_full_pair_still_requires_complete_terminal(self):
        _,_,cad,_=fixture(self.root,'cadical')
        campaign={'started_utc':'2026-10-13T00:00:00+00:00',
                  'solvers':{'kissat':self.solver,'cadical':cad},'catalog':{},'input_manifest':{}}
        with patch.object(verify,'load_census',return_value=(campaign,{'family_counts':{'A':1}},[self.row])):
            for inventory in [False,True]:
                report=verify.verify(self.root,inventory=inventory)
                self.assertEqual(report['verified_UNSAT_runs'],2)
                self.assertEqual(report['status'],'INCOMPLETE')
                with self.assertRaisesRegex(ValueError,'partial'):
                    verify.pack(self.root,self.root/'bad.tar.gz',report)
                self.assertFalse((self.root/'bad.tar.gz').exists())

    def test_pending_pair_is_not_complete(self):
        campaign={'started_utc':'2026-10-13T00:00:00+00:00',
                  'solvers':{'kissat':self.solver,'cadical':{}},'catalog':{},'input_manifest':{}}
        with patch.object(verify,'load_census',return_value=(campaign,{'family_counts':{'A':1}},[self.row])):
            report=verify.verify(self.root,inventory=True)
        self.assertEqual(report['status'],'INCOMPLETE');self.assertEqual(report['missing_runs'],1)

    def test_complete_terminal_and_ledger(self):
        _,_,cad,cad_result=fixture(self.root,'cadical')
        campaign={'started_utc':'2026-10-13T00:00:00+00:00',
                  'solvers':{'kissat':self.solver,'cadical':cad},'catalog':{},'input_manifest':{}}
        terminal={'state':'COMPLETE','completed':2,'total':2,'statuses':{'UNSAT':2},
                  'active':[],'retained_inputs_and_tools_unchanged':True,
                  'families':{'A':{'UNSAT':2}},'native_CPU_seconds':2.5}
        save(self.root/'TERMINAL.json',terminal);save(self.root/'STATUS.json',terminal)
        events=[]
        for result in [self.result,cad_result]:
            event={k:result[k] for k in ('id','family','case_id','solver','status','native_CPU_seconds')}
            event['result']=f'runs/{result["solver"]}/00000/RESULT.json';events.append(event)
        def write_events(rows):
            (self.root/'EVENTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
        write_events(events)
        with patch.object(verify,'load_census',return_value=(campaign,{'family_counts':{'A':1}},[self.row])), \
             patch.object(verify,'check_pins'), patch.object(verify,'COUNTS',{'A':1}):
            self.assertEqual(verify.verify(self.root)['status'],'PASS')
            write_events(events+events[:1])
            with self.assertRaisesRegex(ValueError,'Duplicate/orphan'):
                verify.verify(self.root)
            write_events(events[:1])
            with self.assertRaisesRegex(ValueError,'Incomplete event'):
                verify.verify(self.root)
            write_events(events)
            terminal['native_CPU_seconds']=3.;save(self.root/'TERMINAL.json',terminal)
            save(self.root/'STATUS.json',terminal)
            with self.assertRaisesRegex(ValueError,'CPU total'):
                verify.verify(self.root)

    def test_catalog_formula_and_duplicate_checks(self):
        base=b'1 2 3 4 0\n';header=b'p cnf 7320 156771\n';tail=b'1 0\n'
        row={**self.row,'units':[1],'formula':{'variables':7320,'clauses':156771,
             'bytes':len(header+base+tail),'sha256':hashlib.sha256(header+base+tail).hexdigest()}}
        path=self.root/'rows.gz'
        def write(rows):
            with gzip.open(path,'wt') as f:
                for r in rows:f.write(json.dumps(r)+'\n')
        write([row]);self.assertEqual(len(verify.read_catalog(path,base,{'A':1})),1)
        write([row,row])
        with self.assertRaisesRegex(ValueError,'Nonconsecutive'):verify.read_catalog(path,base,{'A':1})
        row['units']=[2];write([row])
        with self.assertRaisesRegex(ValueError,'formula pin'):verify.read_catalog(path,base,{'A':1})


if __name__=='__main__':unittest.main()
