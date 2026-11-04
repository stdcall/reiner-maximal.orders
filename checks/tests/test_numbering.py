"""Check evaluated counters, native references and finalized PDF outlines."""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile
import unittest

from pypdf import PdfReader, PdfWriter
from pypdf.generic import NullObject

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from build import normalize_outline_destinations
from check_links import check_links


FIXTURE = (
    '#import "/content/book-style.typ": book-style\n'
    '#import "/content/statements.typ": *\n'
    '#import "/content/numbering.typ": continue-sections\n'
    '#show: book-style\n'
    '#set page(numbering: "1")\n'
    '= First chapter <ch:first>\n'
    '#continue-sections()\n'
    '== First section <sec:first>\n'
    '#theorem[First theorem.] <th:first>\n'
    '$ a = a $ <eq:first>\n'
    '== Second section <sec:second>\n'
    '#definition[Second section.] <def:second>\n'
    '{insert}'
    '= Second chapter <ch:second>\n'
    '#continue-sections()\n'
    '== Third section <sec:third>\n'
    '#theorem[Third section.] <th:third>\n'
    'See @sec:third, @th:first, @eq:first and @th:third.\n'
)
EXPRESSION = (
    '(headings: query(heading).map(it => '
    '(level: it.level, position: it.location().position())), '
    'metadata: query(metadata).map(it => it.value))'
)


class NumberingRegression(unittest.TestCase):
    def run_typst(self, root, command, args):
        result = subprocess.run([
            'typst', command, '--root', str(root), '--ignore-system-fonts',
            '--font-path', str(root / 'assets/fonts'), *args],
            text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, '')
        return result.stdout

    def compiled(self, root, insert, last_section):
        driver = root / 'sample.typ'
        driver.write_text(FIXTURE.replace('{insert}', insert))
        raw = root / 'raw.pdf'
        self.run_typst(root, 'compile', [str(driver), str(raw)])
        data = json.loads(self.run_typst(
            root, 'eval', [EXPRESSION, '--in', str(driver)]))
        values = data['metadata']
        chapters = [x['number'] for x in values
                    if x.get('family') == 'heading' and x.get('level') == 1]
        sections = [x['number'] for x in values
                    if x.get('family') == 'heading' and x.get('level') == 2]
        self.assertEqual(chapters, [[1], [2]])
        self.assertEqual(sections, [[n] for n in range(1, last_section + 1)])
        self.assertEqual([x['number'] for x in values
                          if x.get('family') == 'th'],
                         [[1, 1], [last_section, 1]])
        self.assertEqual([x['number'] for x in values
                          if x.get('family') == 'eq'], [[1, 2]])
        self.assertEqual([x['number'] for x in values
                          if x.get('family') == 'def'], [[2, 1]])
        refs = [x for x in values if x.get('kind') == 'cross-reference']
        self.assertEqual({x['target']: x['printed'] for x in refs}, {
            'sec:third': str(last_section), 'th:first': '1.1',
            'eq:first': '1.2', 'th:third': str(last_section) + '.1'})
        check_links(raw, refs)

        original = PdfReader(raw)
        writer = PdfWriter(raw, incremental=True)
        self.assertEqual(normalize_outline_destinations(
            writer, original, left=0), 2 + last_section)
        final = root / 'final.pdf'
        writer.write(final)
        reader = PdfReader(final)
        outline = reader.outline
        self.assertEqual([outline[0].title, outline[2].title],
                         ['Chapter 1. First chapter',
                          'Chapter 2. Second chapter'])
        self.assertEqual(len(outline[1]), last_section - 1)
        self.assertEqual([x.title for x in outline[3]],
                         [f'{last_section}. Third section'])

        def flatten(items):
            for item in items:
                if isinstance(item, list):
                    yield from flatten(item)
                else:
                    yield item

        for destination, heading in zip(flatten(outline), data['headings'],
                                         strict=True):
            position = heading['position']
            self.assertEqual(reader.get_destination_page_number(destination) + 1,
                             position['page'])
            array = destination.dest_array
            self.assertEqual(str(array[1]), '/XYZ')
            self.assertEqual(array[2], 0)
            self.assertIsInstance(array[4], NullObject)
            height = float(reader.pages[position['page'] - 1].mediabox.height)
            expected_top = height - max(0, float(position['y'][:-2]) - 10)
            self.assertAlmostEqual(float(array[3]), expected_top, delta=0.03)

    def test_inserting_section_moves_next_chapter_section_and_statement(self):
        with tempfile.TemporaryDirectory(prefix='reiner-numbering-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            self.compiled(root, '', 3)
            self.compiled(root,
                '== Inserted section <sec:inserted>\nInserted text.\n', 4)

    def test_named_list_cases_move_refs_and_leave_theorem_counter_alone(self):
        with tempfile.TemporaryDirectory(prefix='reiner-cases-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            for inserted, last in (('', 2),
                    ('[#case[Inserted.] <case:inserted>],', 3)):
                driver = root / 'sample.typ'
                driver.write_text(
                    '#import "content/book-style.typ": book-style\n'
                    '#import "content/statements.typ": *\n'
                    '#show: book-style\n'
                    '== Section <sec:section>\n'
                    '#theorem[First.] <th:first>\n'
                    '#case-list([#case[First.] <case:first>],'
                    + inserted + '[#case[Last.] <case:last>])\n'
                    'See case @case:last.\n'
                    '#theorem[Second.] <th:second>\n'
                    '#case-list([#case[Again.] <case:again>])\n')
                pdf = root / 'cases.pdf'
                self.run_typst(root, 'compile', [str(driver), str(pdf)])
                data = json.loads(self.run_typst(root, 'eval',
                    [EXPRESSION, '--in', str(driver)]))
                values = data['metadata']
                self.assertEqual([x['number'] for x in values
                                  if x.get('family') == 'case'],
                                 [[i] for i in range(1, last + 1)] + [[1]])
                self.assertEqual([x['number'] for x in values
                                  if x.get('family') == 'th'],
                                 [[1, 1], [1, 2]])
                refs = [x for x in values
                        if x.get('kind') == 'cross-reference']
                self.assertEqual([x['printed'] for x in refs], [f'({last})'])
                self.assertEqual(check_links(pdf, refs)
                                 ['semantic_references_checked'], 1)

    def test_step_references_omit_terminal_heading_punctuation(self):
        with tempfile.TemporaryDirectory(prefix='reiner-step-refs-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": *\n'
                '#show: book-style\n'
                '== Section <sec:section>\n'
                '#case-list(numbering: "Step 1.",\n'
                '  [#case[First.] <case:first>],\n'
                '  [#case[Second.] <case:second>],\n'
                ')\n'
                'See @case:second. Also (@case:first).\n')
            pdf = root / 'steps.pdf'
            self.run_typst(root, 'compile', [str(driver), str(pdf)])
            values = json.loads(self.run_typst(root, 'eval',
                [EXPRESSION, '--in', str(driver)]))['metadata']
            refs = [x for x in values
                    if x.get('kind') == 'cross-reference']
            self.assertEqual([x['printed'] for x in refs],
                             ['Step 2', 'Step 1'])
            check_links(pdf, refs)
            text = '\n'.join(p.extract_text() for p in PdfReader(pdf).pages)
            self.assertIn('Step 1. First.', text)
            self.assertIn('Step 2. Second.', text)
            self.assertIn('See Step 2. Also (Step 1).', text)

    def test_nested_roman_cases_restore_outer_steps_and_later_list(self):
        with tempfile.TemporaryDirectory(prefix='reiner-nested-cases-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
== Section <sec:section>
#theorem[First theorem.] <th:first>
#case-list(numbering: "Step 1.",
  [#case[
    Outer first.
    #case-list(numbering: "(i)",
      [#case[Inner first.] <case:inner-first>],
      [#case[Inner second.] <case:inner-second>],
    )
  ] <case:outer-first>],
  [#case[Outer second.] <case:outer-second>],
  [#case[Outer third.] <case:outer-third>],
)
#case-list(
  [#case[Later first.] <case:later-first>],
  [#case[Later second.] <case:later-second>],
)
#theorem[After lists.] <th:after>
References: @case:outer-first; @case:inner-first; @case:inner-second;
@case:outer-second; @case:outer-third; @case:later-first; @case:later-second.
''')
            pdf = root / 'nested.pdf'
            self.run_typst(root, 'compile', [str(driver), str(pdf)])
            values = json.loads(self.run_typst(root, 'eval',
                [EXPRESSION, '--in', str(driver)]))['metadata']
            cases = [x for x in values if x.get('family') == 'case']
            self.assertEqual([x['number'] for x in cases],
                             [[1], [1], [2], [2], [3], [1], [2]])
            self.assertEqual([x['number-format'] for x in cases],
                ['Step 1.', '(i)', '(i)', 'Step 1.', 'Step 1.', '(1)', '(1)'])
            self.assertEqual([x['number'] for x in values
                              if x.get('family') == 'th'], [[1, 1], [1, 2]])
            refs = [x for x in values
                    if x.get('kind') == 'cross-reference']
            self.assertEqual([x['printed'] for x in refs],
                ['Step 1', '(i)', '(ii)', 'Step 2', 'Step 3', '(1)', '(2)'])
            self.assertEqual(check_links(pdf, refs)
                             ['semantic_references_checked'], 7)
            text = '\n'.join(p.extract_text() for p in PdfReader(pdf).pages)
            self.assertIn('Step 2. Outer second.', text)
            self.assertIn('Step 3. Outer third.', text)
            self.assertIn('(i) Inner first.', text)
            self.assertIn('(ii) Inner second.', text)
            self.assertIn('(1) Later first.', text)
            self.assertIn('(2) Later second.', text)

    def test_numbered_table_shares_mixed_counter_and_links_to_its_number(self):
        with tempfile.TemporaryDirectory(prefix='reiner-numbered-table-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": *\n'
                '#import "content/main-defs.typ": idx\n'
                '#import "content/index-style.typ": subject-index\n'
                '#show: book-style\n'
                '#set page(numbering: "1")\n'
                '== Section <sec:section>\n'
                '#theorem[Before.] <th:before>\n'
                '#pagebreak()\n'
                '#numbered-table[\n'
                '  #table(columns: 2, [Entry], [Value], [$x_i$], [$i$])\n'
                '] <eq:notation-table>\n'
                '#idx("Notation", target: [@eq:notation-table])\n'
                '$ x=x $ <eq:after>\n'
                'See @eq:notation-table and @eq:after.\n'
                '#subject-index\n')
            pdf = root / 'table.pdf'
            self.run_typst(root, 'compile', [str(driver), str(pdf)])
            values = json.loads(self.run_typst(root, 'eval', [
                'query(metadata).map(it => '
                'if type(it.value) == dictionary and '
                '"position" not in it.value { '
                '(..it.value, position: it.location().position()) '
                '} else { it.value })', '--in', str(driver)]))
            self.assertEqual([x['number'] for x in values
                              if x.get('kind') == 'numbered'
                              and x.get('family') in ('th', 'eq')],
                             [[1, 1], [1, 2], [1, 3]])
            refs = [x for x in values
                    if x.get('kind') == 'cross-reference']
            self.assertEqual([x['printed'] for x in refs[:2]],
                             ['1.2', '1.3'])
            self.assertTrue(all(x['target-position']['page'] == 2
                                for x in refs))
            self.assertEqual(check_links(pdf, refs)
                             ['semantic_references_checked'], 3)
            import fitz
            with fitz.open(pdf) as doc:
                number, = doc[1].search_for('(1.2):')
                first_row, = doc[1].search_for('Entry')
                self.assertLess(number.y1, first_row.y0)

    def test_primed_theorem_tracks_base_without_advancing_the_counter(self):
        with tempfile.TemporaryDirectory(prefix='reiner-variant-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            for inserted, number in (('', 1),
                    ('#theorem[Inserted.] <th:inserted>\n', 2)):
                driver = root / 'sample.typ'
                driver.write_text(
                    '#import "content/book-style.typ": book-style\n'
                    '#import "content/statements.typ": *\n'
                    '#import "content/main-defs.typ": idx\n'
                    '#import "content/index-style.typ": subject-index\n'
                    '#show: book-style\n'
                    '#set page(numbering: "1")\n'
                    '== Section <sec:section>\n' + inserted +
                    '#theorem[Base statement.] <th:base>\n'
                    '#pagebreak()\n'
                    '#theorem-variant[@th:base][Equivalent statement.] '
                    '<th:variant>\n'
                    '#theorem[Next statement.] <th:next>\n'
                    '#idx("Variant", target: [@th:variant])\n'
                    'See @th:base, @th:variant and @th:next.\n'
                    '#subject-index\n')
                pdf = root / 'variants.pdf'
                self.run_typst(root, 'compile', [str(driver), str(pdf)])
                values = json.loads(self.run_typst(root, 'eval', [
                    'query(metadata).map(it => '
                    'if type(it.value) == dictionary and '
                    '"position" not in it.value { '
                    '(..it.value, position: it.location().position()) '
                    '} else { it.value })', '--in', str(driver)]))
                variant, = [x for x in values if x.get('kind') == 'variant']
                self.assertEqual(variant['number'], [1, number])
                self.assertEqual(variant['base'], 'th:base')
                self.assertEqual([x['number'] for x in values
                                  if x.get('kind') == 'numbered'
                                  and x.get('family') == 'th'],
                                 [[1, n] for n in range(1, number + 2)])
                refs = [x for x in values
                        if x.get('kind') == 'cross-reference']
                self.assertEqual([x['printed'] for x in refs[:3]],
                    [f'1.{number}', f'1.{number}′', f'1.{number + 1}'])
                self.assertEqual([x['target-position']['page'] for x in refs],
                                 [1, 2, 2, 2])
                self.assertEqual(check_links(pdf, refs)
                                 ['semantic_references_checked'], 4)
                text = '\n'.join(page.extract_text()
                                 for page in PdfReader(pdf).pages)
                self.assertIn(f'(1.{number}′)', text)

    def test_section_at_page_top_sets_running_head_before_its_body(self):
        with tempfile.TemporaryDirectory(prefix='reiner-running-head-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text(
                '#import "content/book-style.typ": book-style\n'
                '#show: book-style\n'
                '#set page(numbering: "1")\n'
                '== Old section <sec:old>\n'
                'First page.\n#pagebreak()\nSecond page.\n#pagebreak()\n'
                '== New section <sec:new>\n'
                'The page begins with this section.\n\n'
                '== Later section <sec:later>\n'
                'This section starts farther down the same page.\n')
            pdf = root / 'head.pdf'
            self.run_typst(root, 'compile', [str(driver), str(pdf)])
            lines = PdfReader(pdf).pages[2].extract_text().splitlines()
            self.assertEqual(lines[0], '2. New section 3')
            self.assertIn('3. LATER SECTION', lines)

    def test_heading_notes_are_not_repeated_in_contents_or_running_heads(self):
        with tempfile.TemporaryDirectory(prefix='reiner-heading-notes-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/numbering.typ": continue-sections\n'
                '#show: book-style\n'
                '#set page(numbering: "1")\n'
                '#outline(title: none)\n'
                '= Chapter#footnote[Chapter note text.] <ch:first>\n'
                '#continue-sections()\n'
                '== Styled *section#footnote(numbering: _ => "*")['
                'Section note text.]* <sec:first>\n'
                'First paragraph.\n'
                '#pagebreak()\nSecond page.\n'
                '#pagebreak()\nThird page.\n'
                '#pagebreak()\nFourth page.\n')
            pdf = root / 'notes.pdf'
            self.run_typst(root, 'compile', [str(driver), str(pdf)])
            values = json.loads(self.run_typst(root, 'eval', [
                'query(metadata).map(it => it.value)', '--in', str(driver)]))
            placements = [x for x in values
                          if x.get('kind') == 'footnote-placement']
            self.assertEqual(len(placements), 2)
            self.assertTrue(all(x['marker-page'] == x['entry-page']
                                for x in placements))
            original = PdfReader(pdf)
            writer = PdfWriter(pdf, incremental=True)
            normalize_outline_destinations(writer, original, left=0,
                titles=[x for x in values
                        if x.get('kind') == 'bookmark-title'])
            final = root / 'final.pdf'
            writer.write(final)
            reader = PdfReader(final)
            text = '\n'.join(page.extract_text() for page in reader.pages)
            self.assertEqual(text.count('Chapter note text.'), 1)
            self.assertEqual(text.count('Section note text.'), 1)
            self.assertEqual(reader.outline[0].title, 'Chapter 1. Chapter')
            self.assertEqual(reader.outline[1][0].title, '1. Styled section')


if __name__ == '__main__':
    unittest.main()
