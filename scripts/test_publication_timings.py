#!/usr/bin/env python3
"""Failure-focused successful-run timing checks, using tiny synthetic histories."""
from decimal import Decimal
import gzip
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'reproduce'))
import publication_timings as timing


class TimingTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.root=Path(self.tmp.name)
        self.groups={k:{} for k in ('e','abd','closure','balance')}
        self.groups['abd']['A_s00000']={'owner':'A','sha256':'a'*64}
        for i,owner in enumerate(('UU','UT','TU','TT')):
            self.groups['balance']['C2_ROOT_'+owner]={'owner':owner,'sha256':str(i+1)*64}
        self.manifest={'campaigns':{k:{'database':k+'.sqlite3'} for k in ('e','abd','closure')},'files':{}}
        for family in ('e','abd','closure'):
            path=self.root/(family+'.sqlite3');db=sqlite3.connect(path)
            db.execute('CREATE TABLE attempts(case_id,owner,attempt,status,input_sha256,log_sha256,log_gzip,returncode)')
            if family=='abd':
                for attempt,status,cpu,code in [(1,'TIMEOUT','3.00',0),(2,'UNSAT','10.00',20)]:
                    raw=self.log('kissat',cpu,status);blob=gzip.compress(raw,mtime=0)
                    db.execute('INSERT INTO attempts VALUES(?,?,?,?,?,?,?,?)',('A_s00000','A',attempt,status,'a'*64,timing.native.sha(raw),blob,code))
            db.commit();db.close();self.pin(path)
        path=self.root/'cadical/results.sqlite3';path.parent.mkdir();db=sqlite3.connect(path)
        db.execute('CREATE TABLE attempts(key,family,case_id,owner,attempt,status,input_sha256,log_sha256,log_gzip,compressed_log_sha256,returncode)')
        for attempt,status,cpu,code in [(1,'ERROR','4.00',-14),(2,'UNSAT','11.00',20)]:
            raw=self.log('cadical',cpu,status);blob=gzip.compress(raw,mtime=0)
            db.execute('INSERT INTO attempts VALUES(?,?,?,?,?,?,?,?,?,?,?)',('abd/A_s00000','abd','A_s00000','A',attempt,status,'a'*64,timing.native.sha(raw),blob,timing.native.sha(blob),code))
        db.commit();db.close();self.pin(path)
        for cid,case in self.groups['balance'].items():
            for solver in ('kissat','cadical'):
                folder=self.root/'experiment/jobs'/(cid+'_'+solver);folder.mkdir(parents=True)
                raw=self.log(solver,'2.00','UNSAT');blob=gzip.compress(raw,mtime=0)
                log=folder/'native.log.gz';log.write_bytes(blob);self.pin(log)
                receipt={'job_id':cid+'_'+solver,'input_id':cid,'solver':solver,'status':'UNSAT','exit_code':20,
                         'input_sha256_before':case['sha256'],'input_sha256_after':case['sha256'],
                         'native_cpu_seconds':2.0,'user_cpu_seconds':1.5,'sys_cpu_seconds':0.5,
                         'log':{'sha256':timing.native.sha(raw),'gzip_sha256':timing.native.sha(blob)}}
                path=folder/'result.json';path.write_text(json.dumps(receipt));self.pin(path)
        self.save()

    def tearDown(self): self.tmp.cleanup()

    def log(self,solver,cpu,status):
        line=('c process-time: 0s '+cpu+' seconds\n' if solver=='kissat' else
              'c total process time since initialization: '+cpu+' seconds\nc total real time since initialization: 99999999 seconds\n')
        return (line+('s UNSATISFIABLE\nc exit 20\n' if status=='UNSAT' else 'c UNKNOWN\nc exit 0\n')).encode()

    def pin(self,path): self.manifest['files'][path.relative_to(self.root).as_posix()]=timing.native.pin(path)
    def save(self): (self.root/'NATIVE_RELEASE.json').write_text(json.dumps(self.manifest))

    def measure(self):
        with patch.object(timing,'TOTAL',5),patch.object(timing,'FAMILIES',[('A',1),('C2 compatibility',4)]):
            return timing.measure(self.root,self.groups)

    def change_db(self,command,params=(),repin=True):
        path=self.root/'cadical/results.sqlite3';db=sqlite3.connect(path);db.execute(command,params);db.commit();db.close()
        if repin:self.pin(path);self.save()

    def test_successes_once_and_failed_attempts_separate(self):
        result=self.measure();k=result['solvers']['kissat'];c=result['solvers']['cadical']
        for summary,success,overhead in [(k,18,3),(c,19,4)]:
            self.assertEqual(summary['successful_runs'],5);self.assertEqual(summary['all_attempts'],6)
            self.assertEqual(summary['direct_c2_successful_runs'],4)
            self.assertEqual(Decimal(summary['successful_cpu_seconds']),Decimal(success))
            self.assertEqual(Decimal(summary['unsuccessful_cpu_seconds']),Decimal(overhead))
            self.assertEqual(Decimal(summary['all_attempt_cpu_seconds']),Decimal(success+overhead))
        self.assertEqual(k['selected_ordered_input_sha256'],c['selected_ordered_input_sha256'])
        self.assertEqual(c['recorded_attempt_status_counts']['ERROR'],1)

    def test_missing_success_refused(self):
        self.change_db('DELETE FROM attempts WHERE attempt=2')
        with self.assertRaisesRegex(ValueError,'Missing or extra successful'):self.measure()

    def test_interruption_and_timeout_overhead_do_not_reduce_successful_retry(self):
        self.change_db('UPDATE attempts SET attempt=3 WHERE attempt=2')
        raw=self.log('cadical','7.00','INTERRUPTED');blob=gzip.compress(raw,mtime=0)
        self.change_db('INSERT INTO attempts VALUES(?,?,?,?,?,?,?,?,?,?,?)',
            ('abd/A_s00000','abd','A_s00000','A',2,'INTERRUPTED','a'*64,timing.native.sha(raw),blob,timing.native.sha(blob),-15))
        result=self.measure()['solvers']['cadical']
        self.assertEqual(Decimal(result['successful_cpu_seconds']),Decimal(19))
        self.assertEqual(Decimal(result['unsuccessful_cpu_seconds']),Decimal(11))
        self.assertEqual(result['unsuccessful_attempts'],2)

    def test_duplicate_success_refused(self):
        self.change_db('INSERT INTO attempts SELECT key,family,case_id,owner,3,status,input_sha256,log_sha256,log_gzip,compressed_log_sha256,returncode FROM attempts WHERE attempt=2')
        with self.assertRaisesRegex(ValueError,'More than one successful'):self.measure()

    def test_attempt_after_success_refused(self):
        self.change_db('INSERT INTO attempts SELECT key,family,case_id,owner,3,status,input_sha256,log_sha256,log_gzip,compressed_log_sha256,returncode FROM attempts WHERE attempt=1')
        with self.assertRaisesRegex(ValueError,'follows selected terminal'):self.measure()

    def test_cross_solver_input_identity_mismatch_refused(self):
        self.change_db("UPDATE attempts SET input_sha256=? WHERE attempt=2",('b'*64,))
        with self.assertRaisesRegex(ValueError,'differs from selected formula'):self.measure()

    def test_changed_capsule_database_refused(self):
        self.change_db("UPDATE attempts SET owner='B'",repin=False)
        with self.assertRaisesRegex(ValueError,'authenticated capsule pin'):self.measure()

    def test_mismatched_direct_resource_usage_refused(self):
        path=self.root/'experiment/jobs/C2_ROOT_UU_cadical/result.json';r=json.loads(path.read_text())
        r['user_cpu_seconds']=30;path.write_text(json.dumps(r));self.pin(path);self.save()
        with self.assertRaisesRegex(ValueError,'child CPU accounting'):self.measure()

    def test_cpu_field_is_unique_and_not_wall_time(self):
        raw=self.log('cadical','1.25','UNSAT')+b'c process time taken by individual solving procedures\nc solving: 200000 seconds\n'
        self.assertEqual(timing.cpu_from_log(raw,'cadical'),Decimal('1.25'))
        self.assertEqual(timing.cpu_from_log(b'c process-time: 1s 1.23 seconds\nc total runtime 99999 seconds\n','kissat'),Decimal('1.23'))
        for bad in (raw+raw,b'c total real time since initialization: 600 seconds\n'):
            with self.assertRaisesRegex(ValueError,'Missing or repeated'):timing.cpu_from_log(bad,'cadical')

    def test_decimal_rounding_and_overhead_identity(self):
        self.assertEqual(timing.hours(Decimal('18')),'0.01')
        bucket=timing.new_bucket();timing.add(bucket,Decimal('12.34'),True);timing.add(bucket,Decimal('3.21'),False)
        self.assertEqual(timing.finish_bucket(bucket)['all_attempt_cpu_seconds'],'15.55')
        bucket['all_attempt_cpu_seconds']+=1
        with self.assertRaisesRegex(ValueError,'do not reconcile'):timing.finish_bucket(bucket)


if __name__=='__main__':unittest.main()
