#!/usr/bin/env python3
"""Public entry point: validate delivered evidence, or create a fresh audit run."""
import argparse,datetime,subprocess,sys
from pathlib import Path
here=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
g=p.add_mutually_exclusive_group();g.add_argument('--run',action='store_true');g.add_argument('--check',action='store_true')
p.add_argument('--run-dir',type=Path)
a=p.parse_args()
if a.run:
    target=(a.run_dir or here/'runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')).resolve()
    if not target.is_relative_to(here) or target.exists():p.error('choose a new directory inside this audit package')
    print('Fresh audit directory:',target,flush=True)
    args=['--run','--run-dir',str(target)]
else:
    target=(a.run_dir or here/'fresh').resolve()
    args=['--run-dir',str(target)]
sys.exit(subprocess.call([sys.executable,str(here/'verify_all_declarations.py'),*args]))
