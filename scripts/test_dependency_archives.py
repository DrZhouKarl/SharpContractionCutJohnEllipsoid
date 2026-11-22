#!/usr/bin/env python3
"""Offline regression checks for source archives, symlinks and installer resume."""

import argparse
from contextlib import redirect_stdout
from datetime import datetime, timezone
import importlib.util
import io
import json
from pathlib import Path
import shutil
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('fetch_dependencies', ROOT/'scripts/fetch_dependencies.py')
installer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(installer)
REVISION = '0a6c8e0355da0405d616f80b9f8232c4fab2cc5b'
ARCHIVE = None


class ArchiveChecks(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='sharpcut-archive-check-')
        self.addCleanup(self.temporary.cleanup)
        self.work = Path(self.temporary.name)
        self.target = self.work/'package'
        self.top = 'package-'+REVISION

    def archive(self, entries):
        path = self.work/'archive.tar.gz'
        with tarfile.open(path, 'w:gz') as stream:
            root = tarfile.TarInfo(self.top)
            root.type = tarfile.DIRTYPE
            stream.addfile(root)
            for name, kind, value in entries:
                info = tarfile.TarInfo(self.top+'/'+name)
                info.type = kind
                info.mode = 0o755
                if kind == tarfile.REGTYPE:
                    data = value.encode()
                    info.size = len(data)
                    stream.addfile(info, io.BytesIO(data))
                else:
                    info.linkname = value
                    stream.addfile(info)
        return path

    def test_internal_forward_and_parent_relative_links(self):
        archive = self.archive([
            ('bin/lean.py', tarfile.SYMTYPE, 'lean'),
            ('bin/lean', tarfile.REGTYPE, '#!/bin/sh\n'),
            ('scripts/run', tarfile.SYMTYPE, '../bin/lean'),
        ])
        installer.unpack(archive, self.target, REVISION)
        self.assertTrue((self.target/'bin/lean.py').is_symlink())
        self.assertEqual((self.target/'scripts/run').read_text(), '#!/bin/sh\n')
        self.assertEqual(installer.source_links(self.target),
                         {'bin/lean.py': 'lean', 'scripts/run': '../bin/lean'})
        self.assertEqual(list(installer.source_hashes(self.target)), ['bin/lean'])

    def test_absolute_link_rejected(self):
        archive = self.archive([('bad', tarfile.SYMTYPE, '/tmp/outside')])
        with self.assertRaisesRegex(RuntimeError, 'Unsafe symbolic link'):
            installer.unpack(archive, self.target, REVISION)
        self.assertFalse(self.target.exists())

    def test_escaping_relative_link_rejected(self):
        archive = self.archive([('bin/bad', tarfile.SYMTYPE, '../../../outside')])
        with self.assertRaisesRegex(RuntimeError, 'Unsafe symbolic link'):
            installer.unpack(archive, self.target, REVISION)
        self.assertFalse(self.target.exists())

    def test_member_path_traversal_rejected(self):
        archive = self.archive([('../outside', tarfile.REGTYPE, 'bad')])
        with self.assertRaisesRegex(RuntimeError, 'Unsafe archive path'):
            installer.unpack(archive, self.target, REVISION)
        self.assertFalse((self.work/'outside').exists())

    def test_write_through_link_rejected(self):
        archive = self.archive([
            ('data', tarfile.DIRTYPE, ''),
            ('alias', tarfile.SYMTYPE, 'data'),
            ('alias/injected', tarfile.REGTYPE, 'bad'),
        ])
        with self.assertRaisesRegex(RuntimeError, 'symbolic-link parent'):
            installer.unpack(archive, self.target, REVISION)

    def test_link_cycle_rejected(self):
        archive = self.archive([('a', tarfile.SYMTYPE, 'b'), ('b', tarfile.SYMTYPE, 'a')])
        with self.assertRaisesRegex(RuntimeError, 'Unresolvable symbolic link'):
            installer.unpack(archive, self.target, REVISION)
        self.assertFalse(self.target.exists())

    def test_duplicate_member_rejected(self):
        archive = self.archive([('file', tarfile.REGTYPE, 'a'), ('file', tarfile.REGTYPE, 'b')])
        with self.assertRaisesRegex(RuntimeError, 'Duplicate archive path'):
            installer.unpack(archive, self.target, REVISION)

    def test_special_member_rejected(self):
        archive = self.archive([('fifo', tarfile.FIFOTYPE, '')])
        with self.assertRaisesRegex(RuntimeError, 'Unsupported source archive entry'):
            installer.unpack(archive, self.target, REVISION)

    def test_existing_package_preserved(self):
        self.target.mkdir()
        (self.target/'keep').write_text('user data')
        archive = self.archive([('file', tarfile.REGTYPE, 'new')])
        with self.assertRaisesRegex(RuntimeError, 'existing package'):
            installer.unpack(archive, self.target, REVISION)
        self.assertEqual((self.target/'keep').read_text(), 'user data')

    def test_actual_mathlib_archive_and_offline_resume(self):
        if ARCHIVE is None:
            self.skipTest('Pass --archive for the actual mathlib regression')
        # Use the user's authenticated archive and the complete real baseline.
        (self.work/'environment').mkdir()
        shutil.copy2(ROOT/'environment/baseline.json', self.work/'environment/baseline.json')
        shutil.copytree(ROOT/'environment/source-receipts', self.work/'environment/source-receipts')
        archives = self.work/'.lake/source-archives'
        archives.mkdir(parents=True)
        copy = archives/ARCHIVE.name
        shutil.copy2(ARCHIVE, copy)
        with patch.object(installer, 'ROOT', self.work), patch.object(sys, 'argv', ['installer', '--offline']), \
                patch.object(installer, 'download', side_effect=AssertionError('Offline mode made a request')):
            with redirect_stdout(io.StringIO()):
                self.assertEqual(installer.main(), 1)  # The other eight archives are intentionally absent.
            target = self.work/'.lake/packages/mathlib'
            expected = {'scripts/bench/build/fake-root/bin/lean.py': 'lean',
                        'scripts/bench/size/run.py': 'run'}
            self.assertEqual(installer.source_links(target), expected)
            for relative in expected:
                self.assertTrue((target/relative).is_symlink())
                self.assertTrue((target/relative).resolve().is_file())
            receipt = json.loads((self.work/'environment/source-receipts/mathlib.json').read_text())
            self.assertEqual(receipt['symlinks'], expected)
            with tarfile.open(ARCHIVE, 'r:gz') as stream:
                members = stream.getmembers()
                self.assertEqual(len(receipt['files']), sum(member.isfile() for member in members))
                source = 'Mathlib/Data/Real/Basic.lean'
                archived = stream.extractfile('mathlib4-'+REVISION+'/'+source).read()
                self.assertEqual((target/source).read_bytes(), archived)
            with redirect_stdout(io.StringIO()) as resumed:
                self.assertEqual(installer.main(), 1)
            self.assertIn('Validated existing pinned sources: mathlib', resumed.getvalue())
            # Even a retargeting to another package-internal file is detected.
            link = target/'scripts/bench/size/run.py'
            link.unlink()
            link.symlink_to('../build/fake-root/bin/lean')
            with redirect_stdout(io.StringIO()):
                self.assertEqual(installer.main(), 1)
            state = json.loads((self.work/'.lake/dependency-preparation.json').read_text())
            self.assertIn('does not match its pinned receipt', state['error'])


def main():
    global ARCHIVE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    ARCHIVE = args.archive.resolve() if args.archive else None
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ArchiveChecks)
    started = datetime.now(timezone.utc).isoformat()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps({
        'started_utc': started, 'finished_utc': datetime.now(timezone.utc).isoformat(),
        'command': [sys.executable, *sys.argv], 'success': result.wasSuccessful(),
        'tests_run': result.testsRun, 'skipped': len(result.skipped), 'network_requests': 0,
        'failures': [str(test) for test, _ in result.failures],
        'errors': [str(test) for test, _ in result.errors],
        'actual_archive_sha256': installer.digest(ARCHIVE) if ARCHIVE else None,
        'installer_sha256': installer.digest(ROOT/'scripts/fetch_dependencies.py'),
        'scope': 'Archive extraction and resume regression; not Lean proof certification.'
    }, indent=2)+'\n')
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    raise SystemExit(main())
