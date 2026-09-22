"""Check that changed local sources are never reported as the pinned upstream code.

Inputs: upstream_sources.read_source, exercised on a temporary directory. Output: unittest results.
Requires scripts/upstream_sources.py.
"""

import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from upstream_sources import SOURCES, read_source


class SourceIntegrityTests(unittest.TestCase):
    def test_local_content_must_match_the_pin(self):
        content = b"int example(void) { return 0; }\n"
        entry = ("https://invalid.example/unused", hashlib.sha256(content).hexdigest())
        with tempfile.TemporaryDirectory() as directory, patch.dict(SOURCES, {"example.c": entry}):
            path = Path(directory) / "example.c"
            path.write_bytes(content)
            self.assertEqual(read_source("example.c", Path(directory)), content)
            path.write_bytes(content.replace(b"return 0", b"return 1"))
            with self.assertRaisesRegex(RuntimeError, "SHA-256 mismatch"):
                read_source("example.c", Path(directory))

    def test_unknown_source_is_rejected(self):
        with self.assertRaises(KeyError):
            read_source("untracked.c")

    def test_missing_local_file_does_not_download(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch("urllib.request.urlopen") as download:
                with self.assertRaises(FileNotFoundError):
                    read_source("quadrules.c", Path(directory))
                download.assert_not_called()


if __name__ == "__main__":
    unittest.main()
