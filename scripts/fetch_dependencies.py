#!/usr/bin/env python3
"""Restore nine exact dependency archives and validate committed source hashes.

Only explicit setup makes HTTPS requests. Verification is offline. No floating
Git revision, automatic retry, redirect, or compiled cache download is used.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import shutil
import subprocess
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    os.replace(temporary, path)


def source_hashes(directory):
    return {str(p.relative_to(directory)): digest(p)
            for p in source_paths(directory) if not p.is_symlink() and p.is_file()}


def source_links(directory):
    """Record link identities themselves, including links to directories."""
    return {str(p.relative_to(directory)): os.readlink(p)
            for p in source_paths(directory) if p.is_symlink()}


def source_paths(directory):
    """Exclude Lake's generated configuration and compilation directories."""
    files = []
    for base, dirs, names in os.walk(directory, followlinks=False):
        dirs[:] = sorted(name for name in dirs if name != '.lake')
        # Lake also caches input-file hashes beside the original input, e.g.
        # widget/package-lock.json.hash. Ignore only a hash with an existing
        # companion input; unrelated extra files still fail source validation.
        files.extend(Path(base)/name for name in names
                     if not (name.endswith('.hash') and (Path(base)/name[:-5]).is_file()))
        files.extend(Path(base)/name for name in dirs if (Path(base)/name).is_symlink())
    return sorted(files)


def download(url, destination):
    """Download one pinned archive without redirects or automatic retries."""
    entry = {'utc': datetime.now(timezone.utc).isoformat(),
             'url': url, 'output': str(destination)}
    temporary = destination.with_suffix(destination.suffix+'.part')
    result = subprocess.run(
        ['curl', '--silent', '--show-error', '--fail', '--retry', '0',
         '--connect-timeout', '30', '--max-time', '300',
         '--proto', '=https', '--output', str(temporary),
         '--write-out', '%{http_code}', url], capture_output=True, text=True)
    entry.update(exit_code=result.returncode, http_status=result.stdout.strip(),
                 error=result.stderr.strip())
    write_json(destination.with_suffix(destination.suffix+'.attempt.json'), entry)
    if result.returncode or result.stdout.strip() != '200':
        raise RuntimeError(f'Download failed without retry: {json.dumps(entry)}')
    os.replace(temporary, destination)
    return entry


def unpack(archive, destination, revision):
    """Preserve internal relative symlinks without writing through archive links."""
    if destination.exists() or destination.is_symlink():
        raise RuntimeError(f'Refusing to replace an existing package: {destination}')
    with tempfile.TemporaryDirectory(prefix='unpack-', dir=destination.parent) as work:
        staging = Path(work)
        with tarfile.open(archive, 'r:gz') as stream:
            members = stream.getmembers()
            if not members:
                raise RuntimeError(f'Empty source archive: {archive}')
            first = PurePosixPath(members[0].name)
            if not first.parts:
                raise RuntimeError('Empty archive member path')
            top = first.parts[0]
            if not top.endswith('-'+revision):
                raise RuntimeError(f'Unexpected revision prefix: {top}')
            paths, links = {}, {}
            for member in members:
                name = PurePosixPath(member.name)
                if not name.parts or name.is_absolute() or '..' in name.parts or name.parts[0] != top:
                    raise RuntimeError(f'Unsafe archive path: {member.name}')
                if name in paths:
                    raise RuntimeError(f'Duplicate archive path: {member.name}')
                paths[name] = member
                if not (member.isdir() or member.isfile() or member.issym()):
                    raise RuntimeError(f'Unsupported source archive entry: {member.name}')
                if member.issym():
                    link = PurePosixPath(member.linkname)
                    resolved = PurePosixPath(posixpath.normpath(str(name.parent/link)))
                    if not member.linkname or link.is_absolute() or not resolved.parts or resolved.parts[0] != top:
                        raise RuntimeError(f'Unsafe symbolic link: {member.name} -> {member.linkname}')
                    links[name] = member.linkname
            for name in paths:
                if any(parent in links for parent in name.parents):
                    raise RuntimeError(f'Archive entry has a symbolic-link parent: {name}')
            # Write all directories and regular files before creating any symlink.
            # This also handles forward links and prevents writes through links.
            for name, member in paths.items():
                target = staging.joinpath(*name.parts)
                if member.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                elif member.isfile():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with stream.extractfile(member) as source, target.open('wb') as output:
                        shutil.copyfileobj(source, output)
                    target.chmod(member.mode & 0o777)
            for name, link in links.items():
                target = staging.joinpath(*name.parts)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.symlink_to(link)
            package_root = (staging/top).resolve()
            for name in links:
                target = staging.joinpath(*name.parts)
                try:
                    resolved = target.resolve()
                except (RuntimeError, OSError) as error:
                    raise RuntimeError(f'Unresolvable symbolic link: {name}') from error
                if not resolved.is_relative_to(package_root):
                    raise RuntimeError(f'Symbolic link escapes the package: {name}')
        if destination.exists() or destination.is_symlink():
            raise RuntimeError(f'Package appeared during extraction: {destination}')
        os.replace(staging/top, destination)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--offline', action='store_true', help='Never make a network request')
    parser.add_argument('--archive-dir', type=Path, help='Read all pinned archives from this existing cache; never modify it')
    args = parser.parse_args()
    baseline = json.loads((ROOT/'environment/baseline.json').read_text())
    archives = ROOT/'.lake/source-archives'
    packages = ROOT/'.lake/packages'
    receipts = ROOT/'environment/source-receipts'
    for directory in [archives, packages]:
        directory.mkdir(parents=True, exist_ok=True)
    report = {'started_utc': datetime.now(timezone.utc).isoformat(), 'success': False,
              'offline': args.offline, 'requests': [], 'packages': [],
              'scope': 'Exact dependency source preparation; no Lean build or proof audit.'}
    try:
        for package in baseline['packages']:
            name, revision = package['name'], package['rev']
            target = packages/name
            receipt_path = receipts/(name+'.json')
            expected = json.loads(receipt_path.read_text())
            if expected['name'] != name or expected['revision'] != revision:
                raise RuntimeError(f'Pinned source receipt mismatch: {name}')
            if target.exists():
                if expected['files'] != source_hashes(target) or expected.get('symlinks', {}) != source_links(target):
                    raise RuntimeError(f'Existing package does not match its pinned receipt: {name}')
                print(f'Validated existing pinned sources: {name}', flush=True)
            else:
                archive = (args.archive_dir or archives)/(name+'-'+revision+'.tar.gz')
                if not archive.is_file():
                    if args.offline or args.archive_dir:
                        raise RuntimeError(f'Missing pinned archive: {archive}')
                    print(f'Fetching {name} at {revision}', flush=True)
                    report['requests'].append(download(expected['url'], archive))
                if digest(archive) != expected['archive_sha256']:
                    raise RuntimeError(f'Archive checksum does not match the committed receipt: {name}')
                unpack(archive, target, revision)
                if expected['files'] != source_hashes(target) or expected.get('symlinks', {}) != source_links(target):
                    raise RuntimeError(f'Extracted package does not match its pinned source hashes: {name}')
                print(f'Prepared {name}: {len(expected["files"])} source files', flush=True)
            report['packages'].append({'name':name, 'revision':revision, 'receipt_sha256':digest(receipt_path)})
        if (packages/'mathlib/lean-toolchain').read_text().strip() != baseline['lean_toolchain']:
            raise RuntimeError('mathlib/toolchain mismatch')
        inherited = {p['name']:p['rev'] for p in json.loads((packages/'mathlib/lake-manifest.json').read_text())['packages']}
        wanted = {p['name']:p['rev'] for p in baseline['packages'] if p['name'] != 'mathlib'}
        if inherited != wanted:
            raise RuntimeError('mathlib transitive pins do not match the committed baseline')
        report['success'] = True
        print('PASS: all nine exact source packages are ready; no compiled cache was downloaded.')
    except Exception as error:
        report['error'] = str(error)
        print(f'ERROR: {error}', flush=True)
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        write_json(ROOT/'.lake/dependency-preparation.json', report)
    return 0 if report['success'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
