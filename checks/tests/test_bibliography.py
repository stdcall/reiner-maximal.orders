"""Compile bibliography fixtures with the production reader and renderer."""
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
BIB_KEY = re.compile(r'(?m)^@[A-Za-z]+\{([^,]+),')


def bib_keys():
    return BIB_KEY.findall((ROOT / 'references.bib').read_text())


class Bibliography(unittest.TestCase):
    def fixture(self, root):
        shutil.copytree(ROOT / 'content', root / 'content')
        shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
        shutil.copyfile(ROOT / 'references.bib', root / 'references.bib')
        (root / 'sample.typ').write_text(
            '#import "content/book-style.typ": book-style\n'
            '#import "content/statements.typ": bib-item\n'
            '#import "content/bibliography-style.typ": '
            'bib-group, bib-description\n'
            '#show: book-style\n'
            '#set page(header: none, footer: none, numbering: "1")\n'
            'Mention @bib:Kaplansky1970 and again @bib:Kaplansky1970.\n'
            '#footnote[Another mention @bib:Kaplansky1970.]\n'
            '#pagebreak()\nSecond page @bib:Kaplansky1970.\n'
            '#pagebreak()\n'
            '#metadata((kind: "bibliography-boundary", enter: true))\n'
            '#bib-group("Kaplansky1970")\n'
            '#bib-item(tag: "1a")[#bib-description("Kaplansky1970")] '
            '<bib:Kaplansky1970>\n'
            '#bib-item(tag: "1b")[#bib-description("Matsumura1970")] '
            '<bib:Matsumura1970>\n'
            'Internal reference @bib:Kaplansky1970.\n'
            '#metadata((kind: "bibliography-boundary", enter: false))\n')

    def run_typst(self, root, command, *extra):
        result = subprocess.run([
            'typst', command, '--root', str(root), '--ignore-system-fonts',
            '--font-path', str(root / 'assets/fonts'),
            *(['--in', str(root / 'sample.typ'), *extra]
              if command == 'eval' else [str(root / 'sample.typ'), *extra])],
            text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, '')
        return result.stdout

    def compile(self, root, name):
        self.run_typst(root, 'compile', str(root / name))
        with fitz.open(root / name) as doc:
            # Word joiners keep an en dash with its neighbours.
            text = ' '.join(
                ' '.join(p.get_text().replace('\u2060', '').split())
                for p in doc)
            links = [link for page in doc for link in page.get_links()]
        return text, links

    def append_items(self, root, *keys):
        sample = root / 'sample.typ'
        sample.write_text(sample.read_text() + ''.join(
            f'#bib-group("{key}")\n'
            f'#bib-item[#bib-description("{key}")] <bib:{key}>\n'
            for key in keys))

    def test_bib_fields_control_printed_descriptions_and_doi_links(self):
        with tempfile.TemporaryDirectory(prefix='bib-test-', dir='/tmp') as tmp:
            root = Path(tmp)
            self.fixture(root)
            before, links = self.compile(root, 'before.pdf')
            self.assertIn(
                '“Commutative Rings.” Allyn and Bacon, Boston, 1970.', before)
            self.assertIn('Kaplansky, I.', before)
            self.assertNotIn('doi.org', ' '.join(
                str(x.get('uri')) for x in links))
            bib = (root / 'references.bib').read_text()
            for old, new in (
                    ('title = {Commutative Rings}',
                     'title = {Bibliography mutation probe}'),
                    ('author = {Kaplansky, I.}',
                     'author = {Changedauthor, I.}'),
                    ('publisher = {Allyn and Bacon}',
                     'publisher = {Changed publisher},\n'
                     '  doi = {10.1234/mutation-probe}')):
                self.assertEqual(bib.count(old), 1, old)
                bib = bib.replace(old, new)
            (root / 'references.bib').write_text(bib)
            after, links = self.compile(root, 'after.pdf')
            self.assertIn('Bibliography mutation probe', after)
            self.assertIn('Changedauthor', after)
            self.assertIn('Changed publisher', after)
            self.assertNotIn('Commutative Rings', after)
            self.assertIn('https://doi.org/10.1234/mutation-probe',
                          {x.get('uri') for x in links})

    def test_backlinks_are_distinct_pages_and_exclude_internal_references(self):
        with tempfile.TemporaryDirectory(prefix='bib-test-', dir='/tmp') as tmp:
            root = Path(tmp)
            self.fixture(root)
            text, links = self.compile(root, 'book.pdf')
            data = json.loads(self.run_typst(root, 'eval',
                'query(metadata).map(it => (value: '
                'if type(it.value) == dictionary { '
                '(..it.value, position: it.location().position()) '
                '} else { it.value }))'))
            backlinks = [x['value'] for x in data
                         if isinstance(x['value'], dict)
                         and x['value'].get('kind') == 'page-reference']
            self.assertEqual([x['description'] for x in backlinks], ['1', '2'])
            self.assertEqual([x['target-position']['page'] for x in backlinks],
                             [1, 2])
            page_links = [x for x in links
                          if x.get('kind') == fitz.LINK_GOTO
                          and x.get('page') in (0, 1)]
            self.assertGreaterEqual(len(page_links), 2)
            numbers = [x['value']['number'] for x in data
                       if isinstance(x['value'], dict)
                       and x['value'].get('family') == 'bib']
            self.assertEqual(numbers, [['1a'], ['1b']])
            self.assertIn('1a.', text)
            self.assertIn('1b.', text)
            from pypdf import PdfWriter
            sys.path.insert(0, str(ROOT / 'scripts'))
            from check_links import check_links, set_link_descriptions
            writer = PdfWriter(root / 'book.pdf', incremental=True)
            set_link_descriptions(writer, backlinks)
            writer.write(root / 'described.pdf')
            report = check_links(root / 'described.pdf', backlinks)
            self.assertEqual(report['semantic_references_checked'], 2)
            self.assertTrue(all(x['destination-offset-pt'] == 18
                                for x in backlinks))
            wrong = [{k: v for k, v in x.items()
                      if k != 'destination-offset-pt'} for x in backlinks]
            with self.assertRaisesRegex(AssertionError, 'wrong target height'):
                check_links(root / 'described.pdf', wrong)

    def test_related_component_and_journal_fields_reach_pdf(self):
        with tempfile.TemporaryDirectory(prefix='bib-test-', dir='/tmp') as tmp:
            root = Path(tmp)
            self.fixture(root)
            self.append_items(root, 'Brumer1963', 'Amitsur1972', 'Asano1949',
                              'Michler1969')
            before, links = self.compile(root, 'before.pdf')
            self.assertIn('“Structure of Hereditary Orders.” Thesis, '
                          'Princeton Univ. 1963; Bull. Amer. Math. Soc. 69 '
                          '(1963), 721–724; addendum, ibid 70 (1964), 185.',
                          before)
            self.assertIn('DOI (addendum): 10.1090/s0002-9904-1964-11070-3',
                          before)
            self.assertIn('Israel J. Math. 12 (1972), 408–420.', before)
            self.assertIn('Proc. London Math. Soc. (3) 19 (1969)', before)
            uris = {x.get('uri') for x in links}
            self.assertIn(
                'https://doi.org/10.1090/s0002-9904-1964-11070-3', uris)
            bib = (root / 'references.bib').read_text()
            # A field of the related component, the verified abbreviation,
            # and the original spelling where no abbreviation is verified.
            bib = re.sub(r'(?ms)(^@[A-Za-z]+\{Brumer1964,.*?'
                         r'pages = \{)185', r'\g<1>9001--9002', bib)
            bib = re.sub(r'(?ms)(^@[A-Za-z]+\{Amitsur1972,.*?'
                         r'shortjournal = \{)[^}]+',
                         r'\g<1>Journal mutation probe', bib)
            bib = re.sub(r'(?ms)(^@[A-Za-z]+\{Asano1949,.*?)'
                         r'  shortjournal = \{[^}]+\},\n',
                         r'\g<1>  userb = {Original spelling probe},\n', bib)
            (root / 'references.bib').write_text(bib)
            after, _ = self.compile(root, 'after.pdf')
            self.assertIn('(1964), 9001–9002.', after)
            self.assertNotIn('(1964), 185.', after)
            self.assertIn('Journal mutation probe 12 (1972)', after)
            self.assertIn('Original spelling probe 1 (1949)', after)

    def test_special_tags_do_not_advance_the_author_counter(self):
        with tempfile.TemporaryDirectory(prefix='bib-test-', dir='/tmp') as tmp:
            root = Path(tmp)
            self.fixture(root)
            (root / 'sample.typ').write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": bib-item, bib-group\n'
                '#show: book-style\n'
                '#bib-group[First author]\n'
                '#bib-item[One.] <bib:Probe2000>\n'
                '#bib-item(tag: "1a")[Inserted.] <bib:Probe2000a>\n'
                '#bib-item(tag: "1b")[Inserted.] <bib:Probe2000b>\n'
                '#bib-item[Two.] <bib:Probe2001>\n'
                '#bib-group[Second author]\n'
                '#bib-item[One.] <bib:Probe2002>\n')
            data = json.loads(self.run_typst(root, 'eval', 'query(metadata)'))
            numbers = [x['value']['number'] for x in data
                       if isinstance(x['value'], dict)
                       and x['value'].get('family') == 'bib']
            self.assertEqual(numbers, [[1], ['1a'], ['1b'], [2], [1]])

    def test_keys_are_surname_and_year(self):
        sys.path.insert(0, str(ROOT / 'scripts'))
        from lint_typst import label_problem
        for key in bib_keys():
            self.assertRegex(key, r'^[A-Z][A-Za-z]*[0-9]{4}[a-z]?$')
            self.assertIsNone(label_problem('bib:' + key), key)

    def test_entry_file_contains_structure_and_keys_only(self):
        source = (ROOT / 'content/80-bibliography.typ').read_text()
        heading = '#heading(level: 1, numbering: none)[References]'
        keys = []
        groups = 0
        for line in source.splitlines():
            line = line.strip()
            if (not line or line.startswith(('#import', '//', '#metadata'))
                    or line == heading):
                continue
            if re.fullmatch(r'#bib-group\("[A-Za-z][A-Za-z0-9]*"\)', line):
                groups += 1
                continue
            match = re.fullmatch(
                r'#bib-item(?:\(tag: "[0-9]+[ab]?"\))?'
                r'\[#bib-description\("([A-Za-z][A-Za-z0-9]*)"\)\]'
                r' <bib:\1>', line)
            self.assertIsNotNone(match, line)
            keys.append(match[1])
        # The printed list (64 groups, 91 works) and the four works cited
        # but missing from it: DeMeyer-Ingraham (preface), Milnor (Exercise
        # 7.4), van der Waerden (§25) and Feit (§41).
        self.assertEqual((groups, len(keys)), (68, 95))
        self.assertEqual(len(keys), len(set(keys)))
        db_keys = bib_keys()
        self.assertEqual(len(db_keys), len(set(db_keys)))
        self.assertTrue(set(keys) <= set(db_keys))
        related = {key.strip()
                   for group in re.findall(
                       r'(?m)^  related = \{([^}]+)\}',
                       (ROOT / 'references.bib').read_text())
                   for key in group.split(',')}
        inline = {key
                  for path in (ROOT / 'content').rglob('*.typ')
                  if path.name != '80-bibliography.typ'
                  for key in re.findall(
                      r'#bib-description\(\s*"([A-Za-z0-9]+)"\s*,?\s*\)',
                      path.read_text())}
        self.assertEqual(set(db_keys), set(keys) | related | inline,
                         'Every data record is printed, cited inline, '
                         'or a related component')
        cited = {key
                 for path in (ROOT / 'content').rglob('*.typ')
                 for key in re.findall(r'@bib:([A-Za-z0-9]+)',
                                       path.read_text())}
        self.assertTrue(cited <= set(keys), cited - set(keys))
        self.assertTrue({'Curtis1962', 'Deuring1935', 'Swan1970', 'Weil1967',
                         'Bass1968', 'DeMeyer1971', 'Kaplansky1970',
                         'Matsumura1970'} <= set(keys))


if __name__ == '__main__':
    unittest.main()
