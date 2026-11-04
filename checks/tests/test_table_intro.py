"""A table introduction stays with its unbreakable table across page breaks."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import fitz

ROOT = Path(__file__).resolve().parents[2]


class TableIntroduction(unittest.TestCase):
    def test_introduction_table_and_native_reference(self):
        with tempfile.TemporaryDirectory(prefix='reiner-table-intro-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            old_splits = []
            for fill in (25, 40, 55, 70, 85, 100):
                for grouped in (False, True):
                    with self.subTest(fill=fill, grouped=grouped):
                        intro = 'The character table of $A_4$ is given by'
                        opening = (
                            '#numbered-table(introduction: [' + intro + '])['
                            if grouped else intro + '\n#numbered-table[')
                        driver = root / 'sample.typ'
                        driver.write_text(
                            '#import "content/book-style.typ": book-style\n'
                            '#import "content/statements.typ": *\n'
                            '#show: book-style\n'
                            '#set page(width: 260pt, height: 230pt, '
                            'margin: 20pt, header: none, footer: none)\n'
                            '== Probe\n'
                            f'#v({fill}pt)\n' + opening + '\n'
                            '#table(columns: 3, stroke: 0.4pt, '
                            '[Class], [Identity], [Cycle], '
                            '[First], [1], [1], '
                            '[Second], [1], [-1], '
                            '[Third], [2], [0], '
                            '[Fourth], [3], [1])\n'
                            ']<eq:table-intro>\n'
                            'Following paragraph.\n'
                            '#pagebreak()\n'
                            'Reference @eq:table-intro.\n'
                            '$ x = 1 $ <eq:following>\n'
                            'Next @eq:following.\n'
                            '#context {\n'
                            'assert(query(table).len() == 1)\n'
                            'assert(query(metadata).filter(it => '
                            'type(it.value) == dictionary and '
                            'it.value.at("family", default: none) == "eq")'
                            '.len() == 2)\n'
                            '}\n')
                        pdf = root / 'sample.pdf'
                        command = [
                            'typst', 'compile', '--root', str(root),
                            '--ignore-system-fonts', '--font-path',
                            str(root / 'assets/fonts'), str(driver), str(pdf)]
                        result = subprocess.run(command, text=True,
                                                capture_output=True)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertEqual(result.stderr, '')
                        with fitz.open(pdf) as doc:
                            texts = [p.get_text() for p in doc]
                            introduction = next(i for i, t in enumerate(texts)
                                                if 'The character table' in t)
                            table = next(i for i, t in enumerate(texts)
                                         if 'Identity' in t)
                            end = next(i for i, t in enumerate(texts)
                                       if 'Fourth' in t)
                            self.assertEqual(table, end)
                            rules = [path['rect']
                                     for path in doc[table].get_drawings()
                                     if abs(path['width'] - 0.4) < 0.01]
                            self.assertTrue(rules)
                            self.assertAlmostEqual(
                                (min(r.x0 for r in rules)
                                 + max(r.x1 for r in rules)) / 2,
                                doc[table].rect.width / 2, delta=0.2)
                            self.assertEqual(sum(t.count('The character table')
                                                 for t in texts), 1)
                            self.assertIn('(1.1)', texts[table])
                            ref_page = next(p for p in doc
                                            if 'Reference' in p.get_text())
                            self.assertIn('(1.1)', ref_page.get_text())
                            self.assertIn('(1.2)', ref_page.get_text())
                            links = ref_page.get_links()
                            self.assertTrue(any(link.get('page') == table
                                                for link in links))
                            if grouped:
                                self.assertEqual(introduction, table)
                            else:
                                old_splits.append(introduction != table)
            self.assertTrue(any(old_splits),
                            'The old placement must really reproduce a split')


if __name__ == '__main__':
    unittest.main()
