"""Compile the generated index and check its real PDF destinations."""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile
import unittest

import fitz

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_links import check_links
from lint_typst import EXPRESSION


class IndexDestinations(unittest.TestCase):
    def test_late_target_mark_uses_object_start_and_physical_page_order(self):
        with tempfile.TemporaryDirectory(prefix='reiner-index-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": theorem\n'
                '#import "content/main-defs.typ": idx\n'
                '#import "content/index-style.typ": subject-index\n'
                '#show: book-style\n'
                '#set page(numbering: "i", header: none, footer: none)\n'
                '#counter(page).update(5)\n'
                'Before#idx("Sequence")after.\n'
                '#pagebreak()\n'
                '#set page(numbering: "1")\n'
                '#counter(page).update(1)\n'
                '== Named section <sec:named>\n'
                '#theorem[Opening statement.\n'
                '#colbreak()\nContinued statement.\n'
                '#idx("Target", target: [@th:long])\n'
                '] <th:long>\n'
                '#idx("Named section", target: [@sec:named])\n'
                '#idx("Sequence")#idx("Sequence")\n'
                '#subject-index\n')
            flags = ['--root', str(root), '--ignore-system-fonts',
                     '--font-path', str(root / 'assets/fonts')]
            for command, args in (
                    ('compile', [str(driver), str(root / 'sample.pdf')]),
                    ('eval', [EXPRESSION, '--in', str(driver)])):
                result = subprocess.run(['typst', command, *flags, *args],
                                        text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stderr, '')
                if command == 'eval':
                    data = json.loads(result.stdout)
            refs = [item['value'] for item in data['metadata']
                    if isinstance(item['value'], dict)
                    and item['value'].get('kind') == 'cross-reference']
            # Named section, Sequence (v then 2), Target. A repeated mark
            # on the same physical page produces no second locator.
            self.assertEqual([x['target-position']['page'] for x in refs],
                             [2, 1, 3, 2])
            self.assertEqual({x['position']['page'] for x in refs}, {4})
            self.assertEqual(len({x['position']['y'] for x in refs}), 3)
            self.assertEqual(check_links(root / 'sample.pdf', refs)
                             ['semantic_references_checked'], 4)
            with fitz.open(root / 'sample.pdf') as doc:
                self.assertIn('Beforeafter.', doc[0].get_text())
                text = ' '.join(doc[3].get_text().split())
                self.assertIn('Named section 1', text)
                self.assertIn('Sequence v, 2', text)
                self.assertIn('Target 1', text)


if __name__ == '__main__':
    unittest.main()
