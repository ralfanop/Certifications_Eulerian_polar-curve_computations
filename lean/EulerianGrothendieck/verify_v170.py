#!/usr/bin/env python3
"""Rebuild sequentially and audit all declarations against the supplied inventory.
Default: compile every project module. --reuse-matching permits reuse only when
both current source and compiled-object SHA256 match the supplied build record.
In either mode, the axiom audit is re-executed for all 418 declarations.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess

def main():
 p=argparse.ArgumentParser();p.add_argument('--lake');p.add_argument('--memory-mb',type=int,default=4096)
 p.add_argument('--reuse-matching',action='store_true');a=p.parse_args()
 if a.memory_mb<=0:raise SystemExit('Memory limit must be positive')
 root=Path(__file__).resolve().parent;out=root/'verification';out.mkdir(exist_ok=True)
 expected=json.loads((out/'EXPECTED_V170.json').read_text())
 lake=a.lake or shutil.which('lake')
 if not lake:raise SystemExit('Install the pinned Lean toolchain and pass --lake /path/to/lake')
 env=os.environ.copy();env['PATH']=str(Path(lake).resolve().parent)+os.pathsep+env.get('PATH','')
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 def run(args,log):
  q=subprocess.run([lake,*args],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  (out/log).write_text(q.stdout)
  if q.returncode:print(q.stdout);raise SystemExit('Failed: '+log)
  return q.stdout
 version=run(['env','lean','--version'],'LEAN_VERSION_V170.txt')
 if 'version 4.24.0,' not in version:raise SystemExit('Wrong Lean version')
 manifest=json.loads((root/'lake-manifest.json').read_text())
 assert next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')==expected['mathlib']
 reused=[];compiled=[]
 for mod in expected['modules']:
  rel=mod.replace('.','/')+'.lean';src=root/rel
  if sha(src)!=expected['source_sha256'][rel]:raise SystemExit('Source identity mismatch: '+rel)
  obj=root/'.lake/build/lib/lean'/rel.replace('.lean','.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  if a.reuse_matching and obj.exists() and sha(obj)==expected['compiled_object_sha256'][rel]:
   reused.append(mod)
  else:
   run(['env','lean',f'-M{a.memory_mb}','-o',str(obj),str(src)],mod.replace('.','_')+'_BUILD.txt')
   compiled.append(mod)
  print(('Reused verified hashes: ' if mod in reused else 'Compiled: ')+mod,flush=True)
 run(['env','lean',f'-M{a.memory_mb}','-o',str(root/'.lake/build/lib/lean/EulerianGrothendieck.olean'),'EulerianGrothendieck.lean'],'ROOT_V170_BUILD.txt')
 audit='import EulerianGrothendieck\n'+''.join('#print axioms '+n+'\n#check '+n+'\n' for n in expected['theorems'])
 (root/'AuditV170.lean').write_text(audit)
 log=run(['env','lean',f'-M{a.memory_mb}','AuditV170.lean'],'V170_AXIOMS_AND_STATEMENTS.txt')
 deps={}
 for n,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log):
  axioms={v.strip() for v in axs.split(',') if v.strip()}
  if not axioms<={'propext','Classical.choice','Quot.sound'}:raise SystemExit('Unexpected axiom: '+n+str(axioms))
  deps[n]=sorted(axioms)
 for n in re.findall(r"'([^']+)' does not depend on any axioms",log):deps[n]=[]
 assert set(deps)==set(expected['theorems'])
 for rel,h in expected['source_sha256'].items():assert sha(root/rel)==h,rel
 report=dict(status='PASS',scope=expected['scope'],lean_version=version.strip(),mathlib_revision=expected['mathlib'],
  theorem_count=len(deps),source_module_count=len(expected['modules']),axioms=deps,
  baseline_count=expected['baseline_count'],new_count=expected['new_count'],
  freshly_rebuilt_modules=compiled,source_and_object_hash_reused_modules=reused,
  source_sha256=expected['source_sha256'],
  compiled_object_sha256={rel:sha(root/'.lake/build/lib/lean'/rel.replace('.lean','.olean')) for rel in expected['source_sha256']},
  process_memory_limit_MB=a.memory_mb,concurrency=1)
 (out/'V170_CERTIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
 print('PASS:',len(deps),'declarations; only standard axioms; scope limitations stated in certificate.',flush=True)
if __name__=='__main__':main()
