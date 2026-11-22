#!/usr/bin/env python3
"""Reproduce an accepted proof profile in a new independent offline source copy.

The full-cold mode restores only authenticated source files and symlinks.
Project-cold additionally copies pinned dependency build artifacts and records
that reuse explicitly. Neither mode copies project compilation artifacts.
"""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import subprocess
import sys

from fetch_dependencies import source_hashes, source_links
from verify import source_snapshot

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', required=True, type=Path)
    parser.add_argument('--output-dir', required=True, type=Path)
    parser.add_argument('--profile', choices=['core', 'paper'], default='paper')
    parser.add_argument('--mode', choices=['project-cold', 'full-cold'], required=True)
    args = parser.parse_args()
    destination, output = args.destination.resolve(), args.output_dir.resolve()
    require(not destination.exists(), f'Refusing to replace source copy: {destination}')
    require(not output.exists(), f'Refusing to replace reproduction record: {output}')
    require(not destination.is_relative_to(ROOT), 'Reproduction must be outside the development source root')
    require(not output.is_relative_to(destination), 'Reproduction logs must be outside the independent source root')
    output.mkdir(parents=True)
    record = {
        'started_utc': datetime.now(timezone.utc).isoformat(), 'success': False,
        'profile': args.profile, 'mode': args.mode,
        'independent_source_root': str(destination), 'network_requests': 0,
        'dependency_artifacts_reused': args.mode == 'project-cold',
        'project_artifacts_reused': False, 'packages': [],
    }

    def save():
        (output/'reproduction.json').write_text(json.dumps(record, indent=2)+'\n')

    try:
        save()
        snapshot = source_snapshot()
        record['development_source_snapshot'] = snapshot
        destination.mkdir(parents=True)
        for name in snapshot:
            source, target = ROOT/name, destination/name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
        # Include the public specifications in the independent source project.
        for source in ROOT.glob('*.md'):
            shutil.copy2(source, destination/source.name)
        for name in ['LICENSE', 'NOTICE']:
            if (ROOT/name).is_file():
                shutil.copy2(ROOT/name, destination/name)

        manifest = json.loads((ROOT/'lake-manifest.json').read_text())
        for package in manifest['packages']:
            source, target = ROOT/package['dir'], destination/package['dir']
            receipt = json.loads((ROOT/package['sourceReceipt']).read_text())
            require(source_hashes(source) == receipt['files'], f'Unauthenticated dependency source: {package["name"]}')
            require(source_links(source) == receipt.get('symlinks', {}), f'Dependency symlink identity changed: {package["name"]}')
            target.mkdir(parents=True)
            for name in receipt['files']:
                a, b = source/name, target/name
                b.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(a, b)
            # Receipt links are constrained within each package by restoration.
            for name, link in receipt.get('symlinks', {}).items():
                b = target/name
                b.parent.mkdir(parents=True, exist_ok=True)
                b.symlink_to(link)
            if args.mode == 'project-cold' and (source/'.lake/build').is_dir():
                shutil.copytree(source/'.lake/build', target/'.lake/build', symlinks=True)
            require(source_hashes(target) == receipt['files'], f'Copied dependency source differs: {package["name"]}')
            require(source_links(target) == receipt.get('symlinks', {}), f'Copied dependency symlinks differ: {package["name"]}')
            record['packages'].append({'name': package['name'], 'revision': receipt['revision']})
            save()

        command = [sys.executable, 'scripts/verify.py', '--profile', args.profile,
                   '--output-dir', str(output/'audit'),
                   '--require-cold' if args.mode == 'full-cold' else '--require-project-cold']
        record['verification_command'] = command
        save()
        with (output/'driver.log').open('w') as log:
            result = subprocess.run(command, cwd=destination, stdout=log,
                                    stderr=subprocess.STDOUT, text=True)
        record['exit_code'] = result.returncode
        require(result.returncode == 0, 'Independent verification failed; see driver.log and audit/run.json')
        audit = json.loads((output/'audit/run.json').read_text())
        require(audit['success'], 'Independent verifier did not certify success')
        require(args.profile != 'paper' or audit['full_paper_verified'], 'Independent run did not attain the paper profile')
        require(audit['sources'] == snapshot, 'Independent certified sources differ from the development snapshot')
        require(source_snapshot() == snapshot, 'Development certified sources changed during reproduction')
        record.update(success=True, full_paper_verified=audit['full_paper_verified'],
                      project_audit_entries=audit['project_audit_entries'],
                      legacy_audit_entries=audit['legacy_audit_entries'],
                      verified_named_results=audit['named_paper_results_verified'],
                      verified_supplementary_results=audit['supplementary_results_verified'])
    except Exception as error:
        record['error'] = str(error)
        print(f'FAIL {error}', flush=True)
    finally:
        record['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    if record['success']:
        print(f'PASS independent {args.mode} {args.profile} reproduction', flush=True)
    return 0 if record['success'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
