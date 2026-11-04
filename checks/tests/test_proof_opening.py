"""Proof openings keep their defining display without freezing long prose."""
from pathlib import Path
import shutil
import re
from itertools import product
import subprocess
import tempfile
import unittest

import fitz

ROOT = Path(__file__).resolve().parents[2]


class ProofOpening(unittest.TestCase):
    def test_opening_display_and_note_flow(self):
        with tempfile.TemporaryDirectory(prefix='reiner-proof-opening-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            for length, notes in product((0, 35), (False, True)):
                for fill in (0, 100, 130, 140, 150):
                    with self.subTest(length=length, fill=fill, notes=notes):
                        driver = root / 'sample.typ'
                        driver.write_text(
                            '#import "content/book-style.typ": book-style\n'
                            '#import "content/statements.typ": proof\n'
                            '#show: book-style\n'
                            '#set page(width: 152mm, height: 100mm, '
                            'margin: 17mm, header: none, footer: none)\n'
                            '== Probe\n'
                            f'#v({fill}pt)\n'
                            'Preceding text.\n\n'
                            '#proof['
                            + 'All the maps preserve the given summand. '
                            * length
                            + ('Opening conclusion follows:\n' if length
                               else 'Let $U$ be an $A$-submodule of $L$, '
                               'and let\n')
                            + '$ z = {psi in L^*: psi(U)=0}. $\n'
                            'This completes the argument.\n\n'
                            + 'Additional details follow from the hypothesis. '
                            * 20
                            + '\n\n'
                            'Witness'
                            + ('#footnote[Note entry probe.]' if notes else '')
                            + ' remains '
                            'in the proof.]\n'
                            '#pagebreak()\n'
                            '= Next chapter\n'
                            'Following text.\n')
                        pdf = root / 'sample.pdf'
                        result = subprocess.run([
                            'typst', 'compile', '--root', str(root),
                            '--ignore-system-fonts', '--font-path',
                            str(root / 'assets/fonts'), str(driver),
                            str(pdf)], text=True, capture_output=True)
                        self.assertEqual(result.returncode, 0,
                                         result.stderr)
                        self.assertEqual(result.stderr, '')
                        with fitz.open(pdf) as doc:
                            texts = [p.get_text() for p in doc]
                            tail = next(i for i, t in enumerate(texts)
                                        if ('Opening' if length else
                                            'and let') in t)
                            equation = next(i for i, t in enumerate(texts)
                                            if '𝑧' in t)
                            # The opening-display guarantee covers short
                            # note-free leads. Note runs retain their native
                            # flow; long leads must remain page-breakable.
                            if not length and not notes:
                                self.assertEqual(tail, equation)
                            witness = next(i for i, t in enumerate(texts)
                                           if 'Witness' in t)
                            if notes:
                                entry = next(i for i, t in enumerate(texts)
                                             if 'Note entry probe.' in t)
                                self.assertEqual(witness, entry)
                            self.assertTrue(all(t.strip() for t in texts))
                            if length:
                                self.assertGreater(equation, 0)
                                text = ' '.join(texts)
                                self.assertEqual(text.count('Proof.'), 1)
                                self.assertEqual(len(re.findall(
                                    r'\bAll\b', text)), length)


if __name__ == '__main__':
    unittest.main()
