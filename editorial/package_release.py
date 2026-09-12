#!/usr/bin/env python3
"""Package a committed source tree, final PDFs, and audit-required Git history."""
from pathlib import Path
import datetime,hashlib,io,json,subprocess,tarfile,tempfile,zipfile
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'release'
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT)
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 commit=git('rev-parse','HEAD').decode().strip()
 assert not git('status','--porcelain','--untracked-files=no'),'Commit tracked source changes before packaging.'
 OUT.mkdir(exist_ok=True);prefix=ROOT.name+'/'
 path=OUT/'BFGS_paper_companion_sources.zip'
 forbidden={'.git','.lake','.toolchain','.cache','tmp','scratch','__pycache__','.DS_Store','work'}
 suffixes={'.olean','.ilean','.pyc','.aux','.fls','.fdb_latexmk','.toc'}
 files={};source_names=set(git('ls-tree','-r','--name-only','-z',commit).decode().strip('\0').split('\0'))
 date=datetime.datetime.fromtimestamp(1789199005,datetime.timezone.utc).timetuple()[:6]
 with tempfile.TemporaryDirectory(prefix='pack-',dir=OUT/'work') as tmp:
  bundle=Path(tmp)/'history.bundle';subprocess.run(['git','bundle','create',str(bundle),'HEAD'],cwd=ROOT,check=True)
  with zipfile.ZipFile(path,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9,allowZip64=True) as z:
   def add(name,data,mode=0o644):
    p=Path(name);assert not p.is_absolute() and '..' not in p.parts
    assert not forbidden.intersection(p.parts) and p.suffix not in suffixes,name
    assert name not in files,name
    info=zipfile.ZipInfo(prefix+name,date);info.create_system=3;info.external_attr=(0o100000|mode)<<16;info.compress_type=zipfile.ZIP_DEFLATED
    z.writestr(info,data,compresslevel=9);files[name]={'bytes':len(data),'sha256':sha(data)}
   process=subprocess.Popen(['git','archive','--format=tar',commit],cwd=ROOT,stdout=subprocess.PIPE)
   names=set()
   with tarfile.open(fileobj=process.stdout,mode='r|') as tar:
    for m in tar:
     if m.isdir():continue
     assert m.isfile(),m.name
     add(m.name,tar.extractfile(m).read(),m.mode&0o777);names.add(m.name)
   assert process.wait()==0 and names==source_names
   for folder,filename in [('paper','BFGS_Journal_Article.pdf'),('companion','BFGS_Complete_Companion.pdf')]:
    data=(ROOT/folder/'build/master.pdf').read_bytes();(OUT/filename).write_bytes(data)
    name='release/'+filename
    if name not in files:add(name,data)
    else:assert files[name]['sha256']==sha(data)
   add('_archive/history.bundle',bundle.read_bytes())
   add('_archive/restore_git_history.py',(ROOT/'packaging/restore_git_history.py').read_bytes(),0o755)
   readme=f'''# BFGS paper and complete companion — author-review release

Source commit: {commit}

The outer folder is {ROOT.name}; every repository file retains its exact
relative path. No source files are flattened. The archive includes the full
committed source tree, original corrected research, Lean sources and pinned
dependency records, full correspondence, actual audits, review records, final
PDFs and a Git bundle needed by immutable historical verification checks.

Read release/BFGS_Journal_Article.pdf (article) and
release/BFGS_Complete_Companion.pdf (complete report). Entry points are
paper/master.tex and companion/master.tex. In a fresh extraction restore history
BEFORE building or editing, because the helper checks the original member hashes
and refuses an existing .git:

    python3 _archive/restore_git_history.py
    bash editorial/build.sh
    python3 editorial/verify_historical_baseline.py

The unchanged historical gate is replayed at its exact original release commit.
Its repository-wide citation-only check rejects later editorial Lean additions
at current HEAD; the wrapper preserves that failure and verifies all frozen
inputs before replaying the original gate. Current authoring checks are separate:

    python3 editorial/verify_release_inputs.py

Fresh Lean compilation needs the pinned toolchain/dependencies, omitted from
the archive because they are large reproducible caches. Follow the project
README and bootstrap instructions in a separate verification checkout. Current
fresh-audit commands are documented in editorial/formal_audit/ and
editorial/article_formal/README.md. Existing logs record what actually ran.

The delivered text is for author review. Human metadata, source reading,
responsibility/consent, final novelty assessment and submission/deposit decisions
are reserved to the authors in editorial/AI_AND_AUTHOR_ACTIONS.md.

The manifest _archive/CONTENTS.json hashes every other member. Source snapshots
exclude untracked user changes, dependencies, compiled objects and build debris.
Actual compiler and review logs are evidence and are deliberately retained.
'''
   add('AUTHOR_REVIEW_README.md',readme.encode())
   manifest={'schema_version':1,'source_commit':commit,'root_directory':ROOT.name,'source_paths':'Exact repository-relative paths, preserved without flattening','files':dict(files)}
   add('_archive/CONTENTS.json',(json.dumps(manifest,indent=2)+'\n').encode())
 with zipfile.ZipFile(path) as z:
  assert z.testzip() is None and len(z.namelist())==len(set(z.namelist()))
  assert set(z.namelist())=={prefix+n for n in files}
  for n,r in files.items():assert sha(z.read(prefix+n))==r['sha256'],n
 summary={'status':'PASS','source_commit':commit,'archive':str(path.relative_to(ROOT)),'bytes':path.stat().st_size,'sha256':sha(path.read_bytes()),'members':len(files),'source_files':len(source_names),'original_directory_structure_preserved':True,'excluded':'Dependency caches, raw .git, compiled objects, untracked changes and temporary build files','pdfs':{n:files['release/'+n] for n in ['BFGS_Journal_Article.pdf','BFGS_Complete_Companion.pdf']}}
 (OUT/'SOURCE_MANIFEST.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':
 (OUT/'work').mkdir(parents=True,exist_ok=True)
 main()
