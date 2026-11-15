"""Regression checks for CI verifier dispatch and failure reporting."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('verify_ci', Path(__file__).with_name('verify_ci.py'))
CI = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CI)


class VerifierDispatchTests(unittest.TestCase):
    def dispatch(self, flags, fail_section=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for number in range(2, 8):
                verifier = root / f'section {number}/verify.py'
                verifier.parent.mkdir()
                verifier.touch()
            commands = []

            def run(command, **kwargs):
                commands.append(command)
                return SimpleNamespace(returncode=int(fail_section is not None and
                    Path(command[1]).parent.name == f'section {fail_section}'))

            output = root / 'outputs.txt'
            with patch.object(CI, 'ROOT', root), patch.object(CI, 'audit_foundation'), \
                    patch.object(CI.subprocess, 'run', side_effect=run), \
                    patch.object(sys, 'argv', ['verify_ci.py', *flags]), \
                    patch.dict(os.environ, {'GITHUB_OUTPUT': str(output)}), \
                    contextlib.redirect_stdout(io.StringIO()):
                result = CI.main()
            evidence = root / '.scratch/ci-verified'
            return result, commands, json.loads((evidence / 'summary.json').read_text()), \
                json.loads((evidence / 'durations.json').read_text()), output.read_text()

    def test_ci_uses_lake_artifacts_only_for_section6(self):
        result, commands, summary, durations, output = self.dispatch(['--use-lake-build'])
        self.assertEqual(result, 0)
        self.assertEqual(len(commands), 6)
        self.assertEqual([c[-1] for c in commands if '--use-lake-build' in c], ['--use-lake-build'])
        self.assertIn('section 6', commands[4][1])
        self.assertEqual(commands[4][-1], '--use-lake-build')
        self.assertEqual(commands[1][-1], '--acvf')
        self.assertEqual(set(durations), set(summary))
        self.assertIn('section6=success', output)

    def test_default_and_certified_reuse_modes_remain_available(self):
        result, commands, *_ = self.dispatch([])
        self.assertEqual(result, 0)
        self.assertEqual(len(commands[4]), 2)
        result, commands, *_ = self.dispatch(['--reuse-certified'])
        self.assertEqual(result, 0)
        self.assertEqual(commands[4][-1], '--reuse-certified')

    def test_section_failure_fails_ci_and_retains_other_audits(self):
        result, commands, summary, durations, output = self.dispatch(['--use-lake-build'], fail_section=6)
        self.assertEqual(result, 1)
        self.assertEqual(len(commands), 6)
        self.assertEqual(summary['section6'], 'failure')
        self.assertEqual(summary['section7'], 'success')
        self.assertIn('section6', durations)
        self.assertIn('section6=failure', output)


if __name__ == '__main__':
    unittest.main()
