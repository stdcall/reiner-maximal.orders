from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_indexes import index_checks
from lint_typst import (scan, semantic_checks, label_problem,
    numbering_source_checks, heading_checks, view, MARKUP, CITED, CODE,
    MATH, STRING, COMMENT, coverage_checks, pitfall_checks)
from project import editor_settings, stage


class Scanner(unittest.TestCase):
    def test_modes(self):
        text = 'A #idx(16) b $x_1$ "q" // note\n'
        kinds, ends = scan(text)
        self.assertEqual(kinds[0], MARKUP)
        self.assertEqual(kinds[text.index('idx')], CODE)
        self.assertEqual(kinds[text.index('16')], CODE)
        self.assertEqual(kinds[text.index('x_1')], MATH)
        self.assertEqual(kinds[text.index('"q"')], MARKUP)  # a smart quote
        self.assertEqual(kinds[text.index('note')], COMMENT)
        self.assertIn(text.index(' b'), ends)

    def test_content_blocks_are_prose_and_strings_are_code(self):
        text = '#theorem(title: [Lie])[Body $x$ #idx("Term").]\n'
        kinds, _ = scan(text)
        self.assertEqual(kinds[text.index('Lie')], MARKUP)
        self.assertEqual(kinds[text.index('Body')], MARKUP)
        self.assertEqual(kinds[text.index('Term')], STRING)

    def test_statement_lines(self):
        text = '#let summary = [\n  = Title\n  Text.\n]\n#block(summary)\n'
        kinds, _ = scan(text)
        self.assertEqual(kinds[text.index('Title')], MARKUP)
        self.assertEqual(kinds[text.index('summary)')], CODE)

class PageLabels(unittest.TestCase):
    @staticmethod
    def problems(labels):
        from build import page_label_problems
        return page_label_problems(labels)

    def test_well_formed(self):
        self.assertEqual(self.problems(['', 'i', 'ii', '1', '2', '']),
                         [])
        self.assertEqual(self.problems(['', '', 'v', 'vi', '1']), [])
        self.assertEqual(self.problems(['', 'iii', 'iv', 'v', '1', '2']), [])

    def test_malformed(self):
        for labels in (['1', '1'], ['i', '1', '3'], ['2', '3'], ['1', 'i'],
                       ['i', 'ii'], ['A-1'], ['1', '552a']):
            self.assertTrue(self.problems(labels), labels)

class Index(unittest.TestCase):
    @staticmethod
    def marks(*paths):
        return [{'value': {'kind': 'index-mark', 'path': list(p)}}
                for p in paths]

    def test_paths(self):
        errors, warnings = index_checks(self.marks(
            ('Element', 'nilpotent'), ('Element', 'semisimple')))
        self.assertEqual((errors, warnings), ([], []))

    def test_spelling_variants_and_empty_index(self):
        errors, _ = index_checks(self.marks(
            ('Element', 'nilpotent'), ('element', 'nilpotent')))
        self.assertEqual(len(errors), 1)
        self.assertEqual(index_checks([], final=False), (
            [], ['the index is empty: no #idx marks in the text']))
        self.assertEqual(len(index_checks([], final=True)[0]), 1)

class BibliographyLint(unittest.TestCase):
    def test_unknown_key_and_missing_number_fail_in_draft(self):
        data = {'headings': [], 'equations': [], 'metadata': [
            {'label': None, 'value': {
                'kind': 'cross-reference', 'target': 'bib:Nope2000',
                'resolved': False, 'position': {'page': 1}}},
        ]}
        found = [f for f in semantic_checks(
            data, {}, ROOT, False, {'bib:Adams1969': ('f.typ', 1)},
            {'bib:Nope2000': ('f.typ', 2), 'bib:Adams1969': ('f.typ', 3)})
            if f['rule'] == 'T016']
        self.assertEqual(len(found), 2)
        self.assertTrue(all(f['severity'] == 'error' for f in found))
        self.assertIn('Nope2000', found[0]['message'] + found[1]['message'])

class HeadingNotes(unittest.TestCase):
    def test_multiline_note_keeps_the_heading_label(self):
        text = ('== A title#footnote[\nNote with @sec:elsewhere.\n] '
                '<sec:heading>\n\nParagraph.\n')
        kinds, _ = scan(text)
        markup = view(text, kinds, (MARKUP, CITED))
        self.assertEqual(heading_checks('chapter.typ', text, markup), [])
        missing = text.replace(' <sec:heading>', '')
        kinds, _ = scan(missing)
        markup = view(missing, kinds, (MARKUP, CITED))
        self.assertEqual([x['rule'] for x in
                          heading_checks('chapter.typ', missing, markup)],
                         ['T011'])


class SourceAnchors(unittest.TestCase):
    """T015: the #source(N) anchors, pages of the source edition, stand once
    each and in the order of the pages."""

    @staticmethod
    def anchors(*pages):
        return {'headings': [], 'equations': [], 'metadata': [
            {'label': None, 'value': {'kind': 'source', 'file-page': page,
                                      'position': {'page': 1}}}
            for page in pages]}

    def rules(self, *pages):
        return [f['rule'] for f in semantic_checks(
            self.anchors(*pages), {}, ROOT, True, {}, {})]

    def test_ascending_pages_pass(self):
        self.assertEqual(self.rules(1, 2, 16, 17), [])

    def test_repeated_or_unordered_pages_fail(self):
        self.assertEqual(self.rules(16, 16), ['T015'])
        self.assertEqual(self.rules(17, 16), ['T015'])
        self.assertEqual(self.rules(0), ['T015'])

    def test_anchor_before_display_keeps_the_sentence(self):
        text = 'It follows that\n\n#source(43)\n$\n a = a\n$\n'
        kinds, ends = scan(text)
        self.assertNotIn('T044', [f['rule'] for f in pitfall_checks(
            'content/sample.typ', text, kinds, ends)])

    def test_standalone_anchor_between_prose_still_fails(self):
        text = 'The same statement holds if\n\n#source(43)\n'
        text += 'the group is finite.\n'
        kinds, ends = scan(text)
        self.assertIn('T044', [f['rule'] for f in pitfall_checks(
            'content/sample.typ', text, kinds, ends)])

    def test_multiline_index_call_is_not_an_unfinished_sentence(self):
        text = '#idx(\n  "Tensor product",\n  target: [@sec:tensor],\n)\n'
        text += '\n#source(84)\nLet the algebra have an identity.\n'
        kinds, ends = scan(text)
        self.assertNotIn('T044', [f['rule'] for f in pitfall_checks(
            'content/sample.typ', text, kinds, ends)])


class ProjectContract(unittest.TestCase):
    def test_editor_stage_matches_build(self):
        self.assertIn('--input=stage=' + stage(),
                      editor_settings()['tinymist.typstExtraArgs'])

    def test_required_semantic_prefixes(self):
        for prefix in ('ch', 'sec', 'th', 'def', 'lem', 'prop', 'cor',
                       'exc', 'eq', 'exm'):
            self.assertIsNone(label_problem(prefix + ':sample-object'))
        for label in ('th:1.2', 'def:Group', 'eq:', 'bib:smith1962'):
            self.assertIsNotNone(label_problem(label))
        self.assertIsNone(label_problem('bib:Curtis1962'))

    def test_all_numbered_statements_require_labels(self):
        for helper, prefix in (('theorem', 'th'), ('definition', 'def'),
                ('lemma', 'lem'), ('proposition', 'prop'),
                ('corollary', 'cor'), ('example', 'exm'), ('exercise', 'exc')):
            for suffix, expected in (('', ['T012']),
                                     (' <' + prefix + ':sample>', [])):
                text = '#' + helper + '[Body.]' + suffix + '\n'
                kinds, ends = scan(text)
                found = numbering_source_checks('f.typ', text, kinds, ends)
                self.assertEqual([f['rule'] for f in found], expected,
                                 (helper, suffix))

    def test_final_requires_all_chapters_and_sections(self):
        config = {'completeness': {'chapters': 12, 'sections': 92}}
        data = {'headings': [], 'equations': [], 'metadata': []}
        self.assertEqual(semantic_checks(data, config, ROOT, False, {}), [])
        self.assertEqual([f['rule'] for f in
                          semantic_checks(data, config, ROOT, True, {})],
                         ['T019', 'T019'])
        for level, count in ((1, 12), (2, 92)):
            for n in range(1, count + 1):
                data['metadata'].append({'label': None, 'value': {
                    'kind': 'numbered', 'family': 'heading', 'level': level,
                    'number': [n]}, 'position': {'page': n}})
        # Unlabelled numbered objects remain a separate coverage error.
        self.assertFalse(any(f['rule'] == 'T019' for f in
                         semantic_checks(data, config, ROOT, True, {})))
        data['metadata'][-1]['value']['number'] = [91]
        self.assertTrue(any(f['rule'] == 'T019' for f in
                        semantic_checks(data, config, ROOT, True, {})))


class LeanAudit(unittest.TestCase):
    def test_axioms_and_missing_prints(self):
        sys.path.insert(0, str(ROOT / 'checks/lean'))
        from check_axioms import audit
        record = {'declarations': ['sample']}
        self.assertEqual(audit(record,
            "'sample' depends on axioms: [propext, Classical.choice]", 0), [])
        self.assertTrue(audit(record, "", 0))
        self.assertTrue(audit(record,
            "'sample' depends on axioms: [sorryAx]", 0))

    def test_proof_manifest_matches_sources(self):
        sys.path.insert(0, str(ROOT / 'checks/lean'))
        from check_axioms import load_records
        records, problems = load_records()
        self.assertEqual(problems, [])
        self.assertIsInstance(records, list)

class PdfOutline(unittest.TestCase):
    def test_nested_outlines_keep_height_and_inherit_zoom(self):
        import io
        from pypdf import PdfReader, PdfWriter
        from pypdf.generic import Fit, NullObject
        from build import normalize_outline_destinations
        original = PdfWriter()
        original.add_blank_page(width=300, height=500)
        parent = original.add_outline_item('Chapter', 0,
            fit=Fit.xyz(left=23, top=500, zoom=2))
        original.add_outline_item('Section', 0, parent=parent,
            fit=Fit.xyz(left=34, top=217, zoom=1))
        stream = io.BytesIO()
        original.write(stream)
        stream.seek(0)
        reader = PdfReader(stream)
        writer = PdfWriter(reader)
        self.assertEqual(normalize_outline_destinations(
            writer, reader, left=0), 2)
        result = io.BytesIO()
        writer.write(result)
        result.seek(0)
        checked = PdfReader(result)
        chapter, children = checked.outline
        for destination, top in ((chapter, 500), (children[0], 217)):
            values = destination.dest_array
            self.assertEqual(str(values[1]), '/XYZ')
            self.assertEqual(values[2], 0)
            self.assertEqual(values[3], top)
            self.assertIsInstance(values[4], NullObject)
        self.assertNotIn('/OpenAction', checked.trailer['/Root'])
