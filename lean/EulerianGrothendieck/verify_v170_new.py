#!/usr/bin/env python3
"""Certification run for the NEW V170 modules (Tasks A-I of the 2026-10-29 handoff).

Prerequisite: the baseline run `verify_v170.py` (52 certified modules, unchanged) has
passed in the same workspace.  This script then
  1. deletes any previous compiled objects of the new modules,
  2. compiles the new modules sequentially (one `lean` process at a time, -M <memory-mb>),
  3. runs `AuditNew.lean` (`#print axioms` + `#check` for every new theorem),
  4. checks that only `propext`, `Classical.choice`, `Quot.sound` occur,
  5. records SHA-256 of every new source and compiled object, the Lean and Mathlib
     versions, and writes `verification/V170_NEW_CERTIFICATION.json`.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time

NEW = ["DirichletChiFive", "DirichletChiFiveLFunction", "ComplexArcsineDisk",
       "GaussianFockBridge", "FockVacuumProjection", "CriticalSubcriticalVacuum",
       "UniformParameterVacuum", "CatalanLipschitzDirichlet", "FockCorollaries",
       "BilinearScalarBridge", "VectorOptimum", "ExposedCorrelation", "EndpointDecompositions",
       "BernoulliCumulantIdentification", "ZetaCumulantIdentification", "PrintedAllOrderMajorant",
       "GeneralPhaseOptimization", "OccupancySharpRemainder", "ExplicitNormRemainder"]

def main():
    p = argparse.ArgumentParser(); p.add_argument('--lake'); p.add_argument('--memory-mb', type=int, default=4096)
    a = p.parse_args()
    root = Path(__file__).resolve().parent; out = root / 'verification'; out.mkdir(exist_ok=True)
    lake = a.lake or shutil.which('lake')
    if not lake: raise SystemExit('pass --lake /path/to/lake')
    env = os.environ.copy(); env['PATH'] = str(Path(lake).resolve().parent) + os.pathsep + env.get('PATH', '')
    sha = lambda q: hashlib.sha256(q.read_bytes()).hexdigest()
    def run(args, log):
        t = time.time()
        q = subprocess.run([lake, *args], cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / log).write_text(q.stdout)
        if q.returncode: print(q.stdout); raise SystemExit('Failed: ' + log)
        return q.stdout, round(time.time() - t, 1)
    version, _ = run(['env', 'lean', '--version'], 'LEAN_VERSION_V170_NEW.txt')
    if 'version 4.24.0,' not in version: raise SystemExit('Wrong Lean version: ' + version)
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    mathlib_rev = next(q['rev'] for q in manifest['packages'] if q['name'] == 'mathlib')
    baseline = json.loads((out / 'V170_CERTIFICATION.json').read_text())
    if baseline.get('status') != 'PASS': raise SystemExit('Baseline certificate is not PASS')
    forbidden = re.compile(r'\b(sorry|admit|native_decide|axiom)\b')
    times = {}
    for mod in NEW:
        src = root / 'EulerianGrothendieck' / (mod + '.lean')
        if forbidden.search(src.read_text()): raise SystemExit('Forbidden token in ' + mod)
        obj = root / '.lake/build/lib/lean/EulerianGrothendieck' / (mod + '.olean')
        for ext in ('.olean', '.ilean'):
            q = obj.with_suffix(ext)
            if q.exists(): q.unlink()
        _, dt = run(['env', 'lean', f'-M{a.memory_mb}', '-o', str(obj), '-i', str(obj.with_suffix('.ilean')), str(src)],
                    f'{mod}_NEW_BUILD.txt')
        times[mod] = dt
        print(f'Compiled: EulerianGrothendieck.{mod} ({dt}s)', flush=True)
    log, _ = run(['env', 'lean', f'-M{a.memory_mb}', 'AuditNew.lean'], 'V170_NEW_AXIOMS_AND_STATEMENTS.txt')
    deps = {}
    for n, axs in re.findall(r"^'(.+?)' depends on axioms:\s*\[([^\]]*)\]", log, re.M):
        axioms = {v.strip() for v in axs.split(',') if v.strip()}
        if not axioms <= {'propext', 'Classical.choice', 'Quot.sound'}: raise SystemExit('Unexpected axiom: ' + n + str(axioms))
        deps[n] = sorted(axioms)
    for n in re.findall(r"^'(.+?)' does not depend on any axioms", log, re.M): deps[n] = []
    listed = [l.split(' ', 2)[2].strip() for l in (root / 'AuditNew.lean').read_text().splitlines() if l.startswith('#print axioms')]
    if set(listed) != set(deps): raise SystemExit('Audit mismatch: ' + str(set(listed) ^ set(deps)))
    if 'error' in log.lower(): raise SystemExit('Audit log contains errors')
    rel = lambda mod: 'EulerianGrothendieck/' + mod + '.lean'
    report = dict(status='PASS', scope='New modules of the 2026-10-29 handoff (Tasks A,B,C1,C2,D,E,F,G1,G2,H,I); '
                  'baseline modules untouched (see V170_CERTIFICATION.json)',
                  lean_version=version.strip(), mathlib_revision=mathlib_rev,
                  new_modules=['EulerianGrothendieck.' + m for m in NEW], theorem_count=len(deps), axioms=deps,
                  compile_seconds=times,
                  source_sha256={rel(m): sha(root / rel(m)) for m in NEW},
                  compiled_object_sha256={rel(m): sha(root / '.lake/build/lib/lean/EulerianGrothendieck' / (m + '.olean')) for m in NEW},
                  audit_file_sha256=sha(root / 'AuditNew.lean'),
                  baseline_status=baseline['status'], baseline_theorem_count=baseline['theorem_count'],
                  process_memory_limit_MB=a.memory_mb, concurrency=1)
    (out / 'V170_NEW_CERTIFICATION.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS:', len(deps), 'new declarations; only standard axioms.', flush=True)

if __name__ == '__main__':
    main()
