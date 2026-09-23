"""Owned-job measurement and shared eight-worker admission; never signals foreign jobs."""
import datetime,fcntl,hashlib,json,os,pathlib,re,resource,signal,subprocess,time,uuid
P=pathlib.Path(__file__).resolve().parent
CONTROL=P/'control'
def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def write_json(p,v):
    p=pathlib.Path(p); t=p.with_name(p.name+'.'+uuid.uuid4().hex+'.tmp')
    t.write_text(json.dumps(v,indent=2)+'\n'); os.replace(t,p)
def pressure():
    level=int(subprocess.check_output(['/usr/sbin/sysctl','-n','kern.memorystatus_vm_pressure_level'],text=True))
    text=subprocess.check_output(['/usr/bin/memory_pressure','-Q'],text=True)
    pct=int(re.search(r'free percentage:\s*(\d+)%',text).group(1))
    ram=int(subprocess.check_output(['/usr/sbin/sysctl','-n','hw.memsize'],text=True))
    return level,pct,ram
def acquire(run,expected):
    start=time.monotonic()
    while True:
        with (CONTROL/'admission.lock').open('a+') as serial:
            fcntl.flock(serial,fcntl.LOCK_EX)
            level,pct,ram=pressure(); active=[]; available=[]
            for i in range(8):
                f=(CONTROL/f'slot_{i}.lock').open('a+')
                try: fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
                except BlockingIOError:
                    f.close()
                    try: active.append(json.loads((CONTROL/f'slot_{i}.json').read_text()))
                    except FileNotFoundError: pass
                else: available.append((i,f))
            reserved=sum(max(0,x.get('expected_RSS_bytes',0)-x.get('latest_RSS_bytes',0)) for x in active)
            # Estimates reserve only unmaterialized memory; this is admission, not a per-job limit.
            admit=level==1 and ram*pct/100-reserved>=expected and bool(available)
            chosen=available.pop(0) if admit else None
            for _,f in available: fcntl.flock(f,fcntl.LOCK_UN);f.close()
            if chosen:
                i,f=chosen
                write_json(CONTROL/f'slot_{i}.json',{'run':str(run),'parent_pid':os.getpid(),'owned_pid':None,'expected_RSS_bytes':expected,'latest_RSS_bytes':0,'admitted_utc':utc()})
                return i,f,time.monotonic()-start
        time.sleep(2)
def run_owned(cmd,cwd,env,run,metadata,expected_gib=4):
    expected=int(expected_gib*1024**3);slot,lock,wait=acquire(run,expected)
    before=resource.getrusage(resource.RUSAGE_CHILDREN);start=time.monotonic();peak=0;reason=None;proc=None
    claim={**metadata,'command':cmd,'cwd':str(cwd),'started_utc':utc(),'admission_wait_seconds':wait,'cpu_threads':1,'expected_RSS_bytes_for_admission_only':expected,'wall_deadline':None,'CPU_RSS_file_limits':None,'slot':slot}
    try:
        with (run/'process.log').open('xb') as log:
            proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,pass_fds=(lock.fileno(),))
            claim['owned_pid']=proc.pid;write_json(run/'claim.json',claim)
            while proc.poll() is None:
                rss=0
                try:
                    poll=subprocess.run(['/bin/ps','-o','rss=','-p',str(proc.pid)],capture_output=True,text=True)
                    if poll.returncode==0 and poll.stdout.strip(): rss=int(poll.stdout.strip())*1024;peak=max(peak,rss)
                    elif proc.poll() is None: reason='Owned process RSS monitoring failed'
                    write_json(CONTROL/f'slot_{slot}.json',{'run':str(run),'parent_pid':os.getpid(),'owned_pid':proc.pid,'expected_RSS_bytes':expected,'latest_RSS_bytes':rss,'sampled_utc':utc()})
                    level=int(subprocess.check_output(['/usr/sbin/sysctl','-n','kern.memorystatus_vm_pressure_level'],text=True))
                    if level>=4:
                        rows=[]
                        for f in CONTROL.glob('slot_*.json'):
                            x=json.loads(f.read_text())
                            if x.get('owned_pid') and not x.get('terminal'):rows.append(x)
                        largest=max(rows,key=lambda x:(x.get('latest_RSS_bytes',0),x['owned_pid']),default={})
                        if largest.get('owned_pid')==proc.pid:reason='Actual critical host memory pressure; largest owned compiler/job retired'
                except Exception as exc: reason='Resource monitor failure: '+repr(exc)
                if reason and proc.poll() is None:os.killpg(proc.pid,signal.SIGTERM)
                time.sleep(.5)
            rc=proc.wait()
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        record={**claim,'status':'PASS' if rc==0 and reason is None else 'FAIL','exit_code':rc,'guard_reason':reason,'CPU_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,'elapsed_seconds_informational':time.monotonic()-start,'peak_polled_RSS_bytes':peak,'log_sha256':sha(run/'process.log'),'finished_utc':utc()}
        return record
    except BaseException as exc:
        # Keep admission ownership until the child reaches its natural terminal.
        # A controller cancellation must not free a slot while its job still runs.
        reason='Controller exception; owned job preserved to terminal: '+repr(exc)
        rc=None
        if proc is not None:
            while True:
                try: rc=proc.wait(timeout=.5);break
                except subprocess.TimeoutExpired: continue
                except BaseException: continue
        after=resource.getrusage(resource.RUSAGE_CHILDREN)
        return {**claim,'status':'FAIL','exit_code':rc,'guard_reason':reason,'CPU_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,'elapsed_seconds_informational':time.monotonic()-start,'peak_polled_RSS_bytes':peak,'log_sha256':sha(run/'process.log') if (run/'process.log').exists() else None,'finished_utc':utc()}
    finally:
        write_json(CONTROL/f'slot_{slot}.json',{'terminal':True,'run':str(run),'parent_pid':os.getpid(),'finished_utc':utc()})
        fcntl.flock(lock,fcntl.LOCK_UN);lock.close()
