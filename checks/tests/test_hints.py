"""Exercise/hint links and exclusion of editorial notes in actual PDFs."""
from pathlib import Path
import json
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

import fitz

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_links import check_links, check_hint_links
from lint_typst import EXPRESSION


class ExerciseHints(unittest.TestCase):
    def test_single_paragraph_hint_keeps_legacy_inline_pixels(self):
        with tempfile.TemporaryDirectory(prefix='reiner-hint-inline-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": exercise,hint\n'
                '#show: book-style\n'
                '== Probe <sec:probe>\n'
                '#exercise[Show that the maps preserve the summands. '
                '#hint[@exc:probe][Let the maps preserve each summand. '
                'We therefore have\n$ z = sum_j f_j. $\n'
                ']<hint:probe>]<exc:probe>\n')
            current = root / 'current.pdf'
            self.run_typst(root, 'compile', [str(driver), str(current)], True)
            helper = root / 'content/statements.typ'
            code = helper.read_text()
            # Disable only paragraph grouping, preserving the old inline
            # bracket/equation behavior as the pixel reference.
            code, changed = re.subn(r'if start == end(?: or start == 0)? \{',
                                   'if true {', code)
            self.assertEqual(changed, 1)
            helper.write_text(code)
            legacy = root / 'legacy.pdf'
            self.run_typst(root, 'compile', [str(driver), str(legacy)], True)
            with fitz.open(current) as actual, fitz.open(legacy) as expected:
                self.assertEqual(len(actual), len(expected))
                for a, e in zip(actual, expected):
                    self.assertEqual(a.get_pixmap().samples,
                                     e.get_pixmap().samples)

    def test_final_hint_display_stays_with_breakable_prose_tail(self):
        with tempfile.TemporaryDirectory(prefix='reiner-hint-tail-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            for length in (1, 35):
                for fill in (0, 20, 40, 60, 80):
                    with self.subTest(length=length, fill=fill):
                        driver = root / 'sample.typ'
                        driver.write_text(
                            '#import "content/book-style.typ": book-style\n'
                            '#import "content/statements.typ": exercise,hint\n'
                            '#show: book-style\n'
                            '#set page(width: 240pt, height: 200pt, '
                            'margin: 20pt, header: none, footer: none)\n'
                            '#set math.equation(numbering: "(1)")\n'
                            '== Probe <sec:probe>\n'
                            f'#v({fill}pt)\n'
                            '#exercise[Show the claim. '
                            '#hint[@exc:probe][Earlier paragraph.\n\n'
                            + 'The maps preserve each summand. ' * length
                            + 'Terminal conclusion follows.\n'
                            '$ z = sum_j f_j. $ <eq:tail>\n'
                            ']<hint:probe>]<exc:probe>\n'
                            '#pagebreak()\n'
                            '= Next chapter\n'
                            'See @eq:tail and @exc:probe.\n')
                        pdf = root / 'tail.pdf'
                        self.run_typst(root, 'compile',
                                       [str(driver), str(pdf)], True)
                        with fitz.open(pdf) as doc:
                            texts = [p.get_text() for p in doc]
                            terminal = next(i for i, t in enumerate(texts)
                                            if 'Terminal' in t)
                            equation = next(i for i, t in enumerate(texts)
                                            if '𝑧' in t)
                            self.assertEqual(terminal, equation)
                            self.assertTrue(all(t.strip() for t in texts))
                            self.assertEqual(sum(t.count('Hint:')
                                                 for t in texts), 1)
                            if length == 35:
                                self.assertGreater(equation, 0)
                        data = json.loads(self.run_typst(root, 'eval',
                            [EXPRESSION, '--in', str(driver)], True))
                        values = [x['value'] for x in data['metadata']]
                        refs = [x for x in values
                                if x.get('kind') == 'cross-reference']
                        hints = [x for x in values
                                 if x.get('kind') == 'hint-link']
                        self.assertEqual(check_hint_links(
                            check_links(pdf, refs), hints)['hint_numbers'], 1)
                        self.assertEqual(len(refs), 2)

    def test_math_opening_records_the_clickable_exercise_head(self):
        with tempfile.TemporaryDirectory(prefix='reiner-hint-math-head-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            source = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": exercise, hint
#show: book-style
== Probe <sec:probe>
#heading(level: 3, numbering: none, outlined: false)[Exercises]
#v(FILLpt)
#exercise[
  If $U_i != F_i$, prove that $c_(i i)>1$.
  #hint[@exc:probe][Let $U_i=overline(K)G epsilon_i$. Its socle is simple.]
  <hint:probe>
]<exc:probe>
'''
            for fill in (0, 30, 60):
                with self.subTest(fill=fill):
                    driver = root / 'sample.typ'
                    driver.write_text(source.replace('FILL', str(fill)))
                    pdf = root / 'sample.pdf'
                    self.run_typst(root, 'compile', [str(driver), str(pdf)],
                                   True)
                    data = json.loads(self.run_typst(root, 'eval',
                        [EXPRESSION, '--in', str(driver)], True))
                    values = [x['value'] for x in data['metadata']]
                    refs = [x for x in values
                            if x.get('kind') == 'cross-reference']
                    hints = [x for x in values
                             if x.get('kind') == 'hint-link']
                    result = check_hint_links(check_links(pdf, refs), hints)
                    self.assertEqual(result, {'problems_with_hint': 1,
                        'problems_without_hint': 0, 'hint_numbers': 1})
                    self.assertEqual([x['number'] for x in values
                        if x.get('kind') == 'numbered'
                        and x.get('family') == 'exc'], [[1, 1]])
                    with fitz.open(pdf) as doc:
                        self.assertEqual(sum(p.get_text().count('Hint:')
                                             for p in doc), 1)

    def test_closing_bracket_follows_last_item_of_a_hint_list(self):
        with tempfile.TemporaryDirectory(prefix='reiner-hint-list-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": exercise, hint\n'
                '#show: book-style\n'
                '== Section <sec:section>\n'
                '#exercise[Show the claim. #hint[@exc:claim]['
                '#enum(numbering: "(i)", [First direction.], '
                '[Last direction.])]<hint:claim>]<exc:claim>\n')
            pdf = root / 'list.pdf'
            self.run_typst(root, 'compile', [str(driver), str(pdf)], True)
            with fitz.open(pdf) as doc:
                page = doc[0]
                self.assertEqual(page.get_text().count('Last direction.'), 1)
                last, = page.search_for('Last direction.')
                close, = page.search_for(']')
                self.assertAlmostEqual(last.y0, close.y0, delta=0.05)
                self.assertGreaterEqual(close.x0, last.x1 - 0.1)

    def run_typst(self, root, command, args, notes):
        result = subprocess.run([
            'typst', command, '--root', str(root), '--ignore-system-fonts',
            '--font-path', str(root / 'assets/fonts'),
            '--input', 'editorial-notes=' + ('on' if notes else 'off'),
            *args], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, '')
        return result.stdout

    def test_bidirectional_links_and_no_notes_variant(self):
        with tempfile.TemporaryDirectory(prefix='reiner-hint-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            (root / 'editorial.bib').write_text(
                '@book{Probe2000, author={Probe, A.}, '
                'title={Editorial bibliography probe}, year={2000}}\n')
            driver = root / 'sample.typ'
            driver.write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": exercise, hint, corollary\n'
                '#import "content/main-defs.typ": ed-note, '
                'editorial-bibliography\n'
                '#show: book-style\n'
                '== Exercise section <sec:exercises>\n'
                '#exercise[Show the conclusion. '
                '#hint[@exc:with-hint][Apply the hypothesis.\n\n'
                '$ a=a. $\n] '
                '<hint:with-hint>] <exc:with-hint>\n'
                '#exercise[Another exercise.] <exc:without-hint>\n'
                '#corollary(numbered: false)[Unnumbered statement.] '
                '<cor:unnumbered>\n'
                'See @cor:unnumbered and @cor:unnumbered[the corollary].\n'
                'Text#ed-note[Editorial note probe. #cite(<Probe2000>)]\n'
                '#editorial-bibliography\n')
            for notes in (True, False):
                pdf = root / ('notes.pdf' if notes else 'no-notes.pdf')
                self.run_typst(root, 'compile', [str(driver), str(pdf)], notes)
                data = json.loads(self.run_typst(root, 'eval',
                    [EXPRESSION, '--in', str(driver)], notes))
                metadata = [item['value'] for item in data['metadata']
                            if isinstance(item['value'], dict)]
                hints = [x for x in metadata if x.get('kind') == 'hint-link']
                refs = [x for x in metadata
                        if x.get('kind') == 'cross-reference']
                links = check_links(pdf, refs)
                self.assertEqual(links['semantic_references_checked'], 2)
                self.assertEqual([x['printed'] for x in refs],
                                 ['Corollary', 'Corollary'])
                result = check_hint_links(links, hints)
                self.assertEqual(result, {'problems_with_hint': 1,
                    'problems_without_hint': 1, 'hint_numbers': 1})
                self.assertEqual([x['number'] for x in metadata
                                  if x.get('kind') == 'numbered'
                                  and x.get('family') == 'exc'], [[1, 1], [1, 2]])
                with fitz.open(pdf) as doc:
                    text = ' '.join(p.get_text() for p in doc)
                self.assertEqual('Editorial note probe' in text, notes)
                self.assertEqual('Editorial bibliography probe' in text,
                                 notes)
                self.assertIn('Hint:', text)
                compact = re.sub(r'\s+', '', text)
                self.assertEqual(compact.count('𝑎=𝑎.'), 1)
                self.assertLess(text.index('Apply the hypothesis'),
                                text.index('𝑎'))


if __name__ == '__main__':
    unittest.main()
