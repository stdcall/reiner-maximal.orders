"""Exercise the common layout on a wide numbered system of equations."""
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


class WideDisplay(unittest.TestCase):
    def test_number_and_wide_cases_have_separate_ink(self):
        with tempfile.TemporaryDirectory(prefix='reiner-display-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text(
                '#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": *\n'
                '#show: book-style\n'
                '#set page(header: none, footer: none)\n'
                '== Forms <sec:forms>\n'
                '$ cases(\n'
                ' f(m+n,q)=f(m,q)+f(n,q), quad '
                'f(m,n+q)=f(m,n)+f(m,q),\n'
                ' f(alpha m,n)=alpha f(m,n), quad '
                'f(m,n)=overline(f(n,m)),\n'
                ' f(m,m)>0 quad "for" m!=0.\n'
                ') $ <eq:form-laws>\n')
            result = subprocess.run([
                'typst', 'compile', '--root', str(root),
                '--ignore-system-fonts', '--font-path',
                str(root / 'assets/fonts'), str(driver),
                str(root / 'sample.pdf')], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            with fitz.open(root / 'sample.pdf') as doc:
                page = doc[0]
                number, = page.search_for('(1.1)')
                body = [fitz.Rect(word[:4]) for word in page.get_text('words')
                        if word[4] != '(1.1)'
                        and word[1] < number.y1 + 22
                        and word[3] > number.y0 - 22]
                self.assertTrue(body)
                self.assertGreater(min(r.x0 for r in body), number.x1 + 3)
                self.assertLessEqual(max(r.x1 for r in body),
                                     page.rect.width - 17 * 72 / 25.4 + 0.2)


class EquivalenceScripts(unittest.TestCase):
    def test_subscripts_use_right_side_without_changing_sum_limits_or_refs(self):
        with tempfile.TemporaryDirectory(prefix='reiner-equivalence-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
== Equivalence <sec:equivalence>
$ M ∼_Q N $ <eq:equivalence>
Inline $M ∼_Z N$ and explicit $M scripts(tilde.op)_Q N$.
$ sum_(i=1)^n a_i $
See @eq:equivalence.
''')
            common = ['--root', str(root), '--ignore-system-fonts',
                      '--font-path', str(root / 'assets/fonts')]
            result = subprocess.run(['typst', 'eval', *common,
                '--in', str(driver), 'query(metadata).map(it => it.value)'],
                text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            values = json.loads(result.stdout)
            equation, = [x for x in values if x.get('family') == 'eq']
            self.assertEqual(equation['number'], [1, 1])
            reference, = [x for x in values
                           if x.get('kind') == 'cross-reference']
            self.assertTrue(reference['resolved'])
            self.assertEqual(reference['printed'], '1.1')
            pdf = root / 'sample.pdf'
            result = subprocess.run(['typst', 'compile', *common,
                str(driver), str(pdf)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            check_links(pdf, [reference])
            with fitz.open(pdf) as doc:
                chars = [c for block in doc[0].get_text('rawdict')['blocks']
                         for line in block.get('lines', [])
                         for span in line['spans'] for c in span['chars']]
                relations = [c for c in chars if c['c'] == '∼']
                indices = [c for c in chars if c['c'] in ('𝑄', '𝑍')]
                self.assertEqual(len(relations), 3)
                self.assertEqual(len(indices), 3)
                for relation, index in zip(relations, indices):
                    self.assertGreaterEqual(index['bbox'][0],
                                            relation['bbox'][2] - 0.2)
                    self.assertGreater(index['origin'][1],
                                       relation['origin'][1])
                summation, = [c for c in chars if c['c'] == '∑']
                upper, = [c for c in chars if c['c'] == '𝑛']
                lower, = [c for c in chars if c['c'] == '𝑖'
                          and c['bbox'][0] < summation['bbox'][2]]
                self.assertLess(upper['bbox'][3], summation['bbox'][1])
                self.assertGreater(lower['bbox'][1], summation['bbox'][1])
                self.assertLess(lower['bbox'][0], summation['bbox'][2] - 1)


class ProofFootnotes(unittest.TestCase):
    def test_note_at_proof_end_stays_with_marker_near_page_boundary(self):
        with tempfile.TemporaryDirectory(prefix='reiner-proof-note-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            source = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(height: 130mm, numbering: "1")
#v(FILLpt)
#proof[
  Suppose that the two linear maps have the same kernel. Then their images
  determine a direct decomposition of the module into invariant subspaces.
  $ f(a) = a tau - tau a, quad a in A. $
  Define a new linear homomorphism by the rule
  $ psi'(m) = psi(m) + tau(m), quad m in M. $
  Therefore the first identity implies the second identity, and the new
  homomorphism preserves the action of the algebra.

  Conversely, suppose that there exists a homomorphism satisfying the first
  identity. Define the linear map by taking their difference.
  $ tau(m) = psi^*(m) - psi(m). $
  Then the image is contained in the kernel. Reversing the preceding
  argument, we obtain the required identity
  $ f(a)m = psi(a m) - a psi(m) = (a tau - tau a)m, $
  and this lemma is proved.#footnote[
    The reader should compare this result and the concept of generalized
    derivations with the corresponding construction in the next section.
  ]
]
A second extension problem arises naturally in the theory of algebras and
is described in the following definition.
'''
            for fill in (40, 50, 60):
                with self.subTest(fill=fill):
                    driver = root / 'sample.typ'
                    driver.write_text(source.replace('FILL', str(fill)))
                    common = ['--root', str(root), '--ignore-system-fonts',
                              '--font-path', str(root / 'assets/fonts')]
                    result = subprocess.run(['typst', 'eval', *common,
                        '--in', str(driver),
                        '(metadata: query(metadata).map(it => it.value), '
                        'displays: query(math.equation).filter(it => it.block)'
                        '.map(it => it.location().page()))'],
                        text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    data = json.loads(result.stdout)
                    notes = [x for x in data['metadata']
                             if x.get('kind') == 'footnote-placement']
                    self.assertEqual([(x['marker-page'], x['entry-page'])
                                      for x in notes], [(2, 2)])
                    self.assertEqual(data['displays'][-1], 2)
                    pdf = root / 'sample.pdf'
                    result = subprocess.run(['typst', 'compile', *common,
                        str(driver), str(pdf)], text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stderr, '')
                    with fitz.open(pdf) as doc:
                        self.assertIn('and this lemma is proved.',
                                      doc[1].get_text())
                        self.assertIn('The reader should compare this result',
                                      doc[1].get_text())


class HeadingFootnoteSpacing(unittest.TestCase):
    def test_grouped_heading_preserves_its_normal_gap(self):
        with tempfile.TemporaryDirectory(prefix='reiner-heading-note-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            for level, numbered in ((2, True), (2, False), (3, True), (3, False)):
                gaps = []
                for placement in ('none', 'heading', 'paragraph'):
                    note = '#footnote[An explanatory note.]'
                    heading_note = note if placement == 'heading' else ''
                    paragraph_note = note if placement == 'paragraph' else ''
                    heading = (
                        '=' * level + ' Section title' + heading_note
                        if numbered else
                        f'#heading(level: {level}, numbering: none)'
                        + '[Section title' + heading_note + ']')
                    driver = root / 'sample.typ'
                    driver.write_text(
                        '#import "content/book-style.typ": book-style\n'
                        '#show: book-style\n'
                        '#set page(header: none, footer: none)\n'
                        'Preceding paragraph.\n\n'
                        + heading
                        + '\nThe first paragraph introduces the topic'
                        + paragraph_note + '.\n')
                    pdf = root / 'sample.pdf'
                    result = subprocess.run([
                        'typst', 'compile', '--root', str(root),
                        '--ignore-system-fonts', '--font-path',
                        str(root / 'assets/fonts'), str(driver), str(pdf)],
                        text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stderr, '')
                    with fitz.open(pdf) as doc:
                        self.assertEqual(len(doc), 1)
                        before, = doc[0].search_for('Preceding paragraph.')
                        title, = doc[0].search_for('Section title')
                        gaps.append(title.y0 - before.y1)
                        self.assertGreater(gaps[-1], 0)
                with self.subTest(level=level, numbered=numbered):
                    for gap in gaps[1:]:
                        self.assertAlmostEqual(gap, gaps[0], delta=0.3)


class StatementOpening(unittest.TestCase):
    def test_enum_opening_keeps_heading_with_first_item(self):
        with tempfile.TemporaryDirectory(prefix='reiner-statement-enum-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            source = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(height: 100mm, numbering: "1")
== Tests <sec:tests>
#v(FILLpt)
#lemma[
  #LIST(numbering: "(1)",
    [#case[First condition. The module is projective and its reduction has a
      basis. This condition must remain together with the statement heading
      at a page boundary.] <case:first>],
    [#case[Second condition. The remaining module is free and its generators
      can be chosen compatibly with reduction. Its submodules determine the
      other summands of the decomposition.] <case:second>],
  )
]<lem:opening>
'''
            common = ['--root', str(root), '--ignore-system-fonts',
                      '--font-path', str(root / 'assets/fonts')]
            for listing in ('case-list', 'enum'):
                for fill in (105, 120, 125, 130):
                    with self.subTest(listing=listing, fill=fill):
                        driver = root / 'sample.typ'
                        driver.write_text(source.replace('LIST', listing)
                                          .replace('FILL', str(fill)))
                        result = subprocess.run(['typst', 'eval', *common,
                            '--in', str(driver),
                            'query(metadata).map(it => '
                            '(value:it.value,page:it.location().page()))'],
                            text=True, capture_output=True)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        records = json.loads(result.stdout)
                        lemma, = [x for x in records
                                  if x['value'].get('family') == 'lem']
                        cases = [x for x in records
                                 if x['value'].get('family') == 'case']
                        self.assertEqual(len(cases), 2)
                        self.assertEqual(lemma['page'], cases[0]['page'])
                        if fill == 105:
                            # Keep the list breakable: its second item may
                            # follow on another page when the first fits.
                            self.assertEqual(cases[0]['page'], 1)
                            self.assertEqual(cases[1]['page'], 2)
                        else:
                            self.assertEqual(lemma['page'], 2)
                        pdf = root / 'sample.pdf'
                        result = subprocess.run(['typst', 'compile', *common,
                            str(driver), str(pdf)], text=True,
                            capture_output=True)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertEqual(result.stderr, '')
                        with fitz.open(pdf) as doc:
                            heading = [i for i, page in enumerate(doc)
                                       if page.search_for('Lemma.')]
                            first = [i for i, page in enumerate(doc)
                                     if page.search_for('First condition.')]
                            self.assertEqual(heading, first)
                            self.assertEqual(heading, [lemma['page'] - 1])
                            page = doc[heading[0]]
                            head, = page.search_for('Lemma.')
                            item, = page.search_for('First condition.')
                            self.assertGreater(item.y0, head.y1)

    def test_text_opening_retains_inline_heading(self):
        with tempfile.TemporaryDirectory(prefix='reiner-statement-inline-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            driver = root / 'sample.typ'
            driver.write_text('''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(height: 100mm, numbering: "1")
== Tests <sec:tests>
#v(125pt)
#lemma[Inline opening. The module is projective and its reduction is free.]
''')
            pdf = root / 'sample.pdf'
            result = subprocess.run(['typst', 'compile', '--root', str(root),
                '--ignore-system-fonts', '--font-path',
                str(root / 'assets/fonts'), str(driver), str(pdf)],
                text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            with fitz.open(pdf) as doc:
                page, = [p for p in doc if p.search_for('Lemma.')]
                head, = page.search_for('Lemma.')
                body, = page.search_for('Inline opening.')
                self.assertAlmostEqual(head.y0, body.y0, delta=0.5)
                self.assertGreater(body.x0, head.x1)


class ExerciseOpening(unittest.TestCase):
    def test_math_lead_does_not_collide_with_first_numbered_display(self):
        with tempfile.TemporaryDirectory(prefix='reiner-numbered-lead-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            source = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(height: 100mm, numbering: "1")
== Exercises <sec:exercises>
#v(FILLpt)
#exercise[
  Let $theta$ be a complex-valued class function on a finite group $G$ which
  vanishes on the irregular elements. Show that there exist complex numbers
  $alpha_1,dots,alpha_r$ such that
  $ theta = alpha_1 tau_1 + dots + alpha_r tau_r. $ <eq:expansion>
  The remaining characters form the required basis.
]<exc:expansion>
'''
            common = ['--root', str(root), '--ignore-system-fonts',
                      '--font-path', str(root / 'assets/fonts')]
            for fill in (0, 100, 110):
                with self.subTest(fill=fill):
                    driver = root / 'sample.typ'
                    driver.write_text(source.replace('FILL', str(fill)))
                    result = subprocess.run(['typst', 'eval', *common,
                        '--in', str(driver),
                        'query(metadata).map(it => '
                        '(value:it.value,page:it.location().page()))'],
                        text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    records = json.loads(result.stdout)
                    exercise, = [x for x in records
                                  if x['value'].get('family') == 'exc']
                    equation, = [x for x in records
                                  if x['value'].get('family') == 'eq']
                    self.assertEqual(exercise['page'], equation['page'])
                    pdf = root / 'sample.pdf'
                    result = subprocess.run(['typst', 'compile', *common,
                        str(driver), str(pdf)], text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stderr, '')
                    with fitz.open(pdf) as doc:
                        page = doc[equation['page'] - 1]
                        lead, = page.search_for('such that')
                        tag, = page.search_for('(1.1)')
                        # Include the lead's lowered mathematical indices,
                        # not only the neighbouring Latin text's ink box.
                        lead_ink = [span['bbox'][3]
                            for block in page.get_text('dict')['blocks']
                            for line in block.get('lines', [])
                            for span in line['spans']
                            if lead.y0 - 0.5 <= span['bbox'][1]
                            <= lead.y0 + 7.5]
                        self.assertTrue(lead_ink)
                        self.assertGreater(tag.y0, max(lead_ink) + 0.5)

    def test_short_lead_and_first_display_share_the_exercise_destination(self):
        with tempfile.TemporaryDirectory(prefix='reiner-exercise-lead-',
                                         dir='/tmp') as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / 'content', root / 'content')
            shutil.copytree(ROOT / 'assets/fonts', root / 'assets/fonts')
            source = '''#import "content/book-style.typ": book-style
#import "content/statements.typ": *
#show: book-style
#set page(height: 100mm, numbering: "1")
== Exercises <sec:exercises>
#v(FILLpt)
#exercise[
  Let
  $ e = 1/(m!) lr(sum_(s in S_m) s). $
  Prove that $e$ acts as the identity on every symmetric tensor.
]<exc:symmetrizer>
'''
            for fill in (140, 145, 150):
                with self.subTest(fill=fill):
                    driver = root / 'sample.typ'
                    driver.write_text(source.replace('FILL', str(fill)))
                    common = ['--root', str(root), '--ignore-system-fonts',
                              '--font-path', str(root / 'assets/fonts')]
                    result = subprocess.run(['typst', 'eval', *common,
                        '--in', str(driver),
                        '(records: query(metadata).map(it => '
                        '(value:it.value, page:it.location().page())), '
                        'displays: query(math.equation).filter(it=>it.block)'
                        '.map(it=>it.location().page()))'],
                        text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    data = json.loads(result.stdout)
                    exercise, = [x for x in data['records']
                                 if x['value'].get('family') == 'exc']
                    self.assertEqual(exercise['page'], 2)
                    self.assertEqual(data['displays'], [2])
                    pdf = root / 'sample.pdf'
                    result = subprocess.run(['typst', 'compile', *common,
                        str(driver), str(pdf)], text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    with fitz.open(pdf) as doc:
                        self.assertNotRegex(doc[0].get_text(), r'1\.\s+Let')
                        self.assertRegex(doc[1].get_text(), r'1\.\s+Let')




class ShortProseLead(unittest.TestCase):
    def test_introductory_paragraph_sticks_to_display_or_statement(self):
        with tempfile.TemporaryDirectory(prefix="reiner-prose-lead-", dir="/tmp") as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "content", root / "content")
            shutil.copytree(ROOT / "assets/fonts", root / "assets/fonts")
            for lead, following, needle, offsets in (
                ("Define", "$ X_i=X inter Y_i. $ <eq:filtration>", "(0.1)", (158, 160, 162)),
                ("This yields", "$ X_i=X inter Y_i. $ <eq:filtration>", "(0.1)", (158, 160, 162)),
                ("The above remarks also establish",
                 "#theorem[Let the following statement have enough text to span two lines.] <th:result>",
                 "Theorem.", (150, 155, 160)),
            ):
                for offset in offsets:
                    with self.subTest(lead=lead, offset=offset):
                        source = ('#import "content/book-style.typ": book-style\n'
                                  '#import "content/statements.typ": *\n#show: book-style\n'
                                  '#set page(width:300pt,height:220pt,margin:20pt,header:none,footer:none)\n'
                                  + f"#v({offset}pt)\n{lead}\n\n{following}\n")
                        driver = root / "sample.typ"
                        driver.write_text(source)
                        pdf = root / "sample.pdf"
                        result = subprocess.run([
                            "typst", "compile", "--root", str(root),
                            "--ignore-system-fonts", "--font-path", str(root / "assets/fonts"),
                            str(driver), str(pdf)], text=True, capture_output=True)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertEqual(result.stderr, "")
                        with fitz.open(pdf) as doc:
                            leads = [i for i, page in enumerate(doc) if page.search_for(lead)]
                            targets = [i for i, page in enumerate(doc) if page.search_for(needle)]
                            self.assertEqual(leads, targets)
                            self.assertEqual(len(leads), 1)

    def test_long_paragraph_and_separate_native_list_keep_identical_pixels(self):
        with tempfile.TemporaryDirectory(prefix="reiner-prose-control-", dir="/tmp") as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "content", root / "content")
            shutil.copytree(ROOT / "assets/fonts", root / "assets/fonts")
            source = ('#import "content/book-style.typ": book-style\n'
                      '#import "content/statements.typ": *\n#show: book-style\n'
                      '#set page(width:300pt,height:220pt,margin:20pt,header:none,footer:none)\n'
                      + "CONTROL\n#v(60pt)\n"
                      + "This long ordinary paragraph retains its native paragraph flow and must remain " * 8
                      + "\n\n#case-list(numbering: \"(i)\", [First item.], [Second item.])\n"
                      + "\n#table(columns:2, par[Entry], par[Value], par[Tensor product theorem], [Result])\n"
                      + "A note marker#footnote[Entry\n\nValue] and another#footnote[Short note].\n")
            rendered = []
            for name, control in (("new", ""), ("old", "#show par: it => it\n")):
                driver = root / f"{name}.typ"
                driver.write_text(source.replace("CONTROL\n", control))
                pdf = root / f"{name}.pdf"
                result = subprocess.run(["typst", "compile", "--root", str(root),
                    "--ignore-system-fonts", "--font-path", str(root / "assets/fonts"),
                    str(driver), str(pdf)], text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stderr, "")
                with fitz.open(pdf) as doc:
                    rendered.append([p.get_pixmap(matrix=fitz.Matrix(1.5, 1.5)).samples for p in doc])
            self.assertEqual(*rendered)
            # Math hidden in emph.body excludes this paragraph from prose leads.
            driver = root / "wrapped-math.typ"
            driver.write_text('#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": *\n#show: book-style\n'
                '#set page(width:300pt,height:220pt,margin:20pt,header:none,footer:none)\n'
                '#v(155pt)\n#emph[Compare $A$]\n\n'
                '#theorem[Let the following statement have enough text to span two lines.]\n'
                '\n#let Hom = math.op("Hom")\n#strong[The operator $Hom_K(M,N)$ is native.]\n'
                '#let operator = math.op([H#strong[om]])\n#par[#operator]\n'
                '#metadata((kind: \"native-text-field\", field-type: repr(type(operator.text)), field-func: repr(operator.text.func())))\n')
            pdf = root / "wrapped-math.pdf"
            result = subprocess.run(["typst", "compile", "--root", str(root),
                "--ignore-system-fonts", "--font-path", str(root / "assets/fonts"),
                str(driver), str(pdf)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, "")
            with fitz.open(pdf) as doc:
                lead = [i for i, page in enumerate(doc) if page.search_for("Compare")]
                theorem = [i for i, page in enumerate(doc) if page.search_for("Theorem.")]
                self.assertEqual(lead, [0])
                self.assertEqual(theorem, [1])
            result = subprocess.run(["typst", "eval", "--root", str(root),
                "--ignore-system-fonts", "--font-path", str(root / "assets/fonts"),
                "--in", str(driver),
                'query(metadata.where(value: (kind: "native-text-field", field-type: "content", field-func: "sequence"))).len()'],
                text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, "")
            self.assertEqual(json.loads(result.stdout), 1)


class ShortInlineEquation(unittest.TestCase):
    def test_relation_does_not_split_between_pages(self):
        with tempfile.TemporaryDirectory(prefix="reiner-inline-relation-", dir="/tmp") as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "content", root / "content")
            shutil.copytree(ROOT / "assets/fonts", root / "assets/fonts")
            for offset in (45, 46, 47):
                with self.subTest(offset=offset):
                    source = ('#import "content/book-style.typ": book-style\n#show: book-style\n'
                              '#set page(width:220pt,height:120pt,margin:15pt,header:none,footer:none)\n'
                              + f"#v({offset}pt)\n" + "word " * 22
                              + "$B > B^*$ ends this sentence. More words follow this sentence "
                              + "and provide several lines of ordinary text.\n")
                    driver = root / "sample.typ"
                    driver.write_text(source)
                    pdf = root / "sample.pdf"
                    result = subprocess.run(["typst", "compile", "--root", str(root),
                        "--ignore-system-fonts", "--font-path", str(root / "assets/fonts"),
                        str(driver), str(pdf)], text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stderr, "")
                    with fitz.open(pdf) as doc:
                        letters = [(i, char) for i, page in enumerate(doc)
                            for block in page.get_text("rawdict")["blocks"]
                            for line in block.get("lines", []) for span in line["spans"]
                            for char in span["chars"] if char["c"] == "𝐵"]
                        self.assertEqual(len(letters), 2)
                        self.assertEqual(letters[0][0], letters[1][0])
                        self.assertAlmostEqual(letters[0][1]["origin"][1],
                                               letters[1][1]["origin"][1], delta=0.1)

    def test_long_inline_math_retains_breaks_and_short_native_reference_geometry(self):
        with tempfile.TemporaryDirectory(prefix="reiner-inline-fallback-", dir="/tmp") as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "content", root / "content")
            shutil.copytree(ROOT / "assets/fonts", root / "assets/fonts")
            driver = root / "sample.typ"
            driver.write_text('#import "content/book-style.typ": book-style\n'
                '#import "content/statements.typ": *\n#show: book-style\n'
                '#set page(width:300pt,height:300pt,margin:20pt,header:none,footer:none)\n'
                '== Target <sec:target>\n#theorem[The target statement.] <th:target>\n'
                'The short reference is $a = #ref(<th:target>)$.\n'
                + "A long formula remains breakable: $" + " + ".join(f"x_{i}" for i in range(1, 35))
                + "$ ends here.\n")
            common = ["--root", str(root), "--ignore-system-fonts", "--font-path", str(root / "assets/fonts")]
            result = subprocess.run(["typst", "eval", *common, "--in", str(driver),
                "query(metadata).map(it => it.value)"], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, "")
            values = json.loads(result.stdout)
            refs = [it for it in values if it.get("kind") == "cross-reference"]
            self.assertEqual(len(refs), 1)
            self.assertTrue(refs[0]["resolved"])
            self.assertEqual(refs[0]["printed"], "1.1")
            pdf = root / "sample.pdf"
            result = subprocess.run(["typst", "compile", *common, str(driver), str(pdf)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, "")
            check_links(pdf, refs)
            with fitz.open(pdf) as doc:
                chars = [char for page in doc for block in page.get_text("rawdict")["blocks"]
                         for line in block.get("lines", []) for span in line["spans"]
                         for char in span["chars"] if char["c"] == "𝑥"]
                self.assertEqual(len(chars), 34)
                self.assertGreater(len({round(c["origin"][1], 1) for c in chars}), 1)
                for page in doc:
                    self.assertTrue(all(w[0] >= 19.5 and w[2] <= 280.5 for w in page.get_text("words")))
            # A long equation must keep exactly its previous line/page geometry.
            source = driver.read_text().split("The short reference is")[0]
            source += "A long formula remains breakable: $" + " + ".join(f"x_{i}" for i in range(1, 35)) + "$ ends here.\n"
            style = root / "content/book-style.typ"
            normal = style.read_text()
            pixels = []
            for boxed in (True, False):
                style.write_text(normal if boxed else normal.replace(
                    "if ink.width <= 12em.to-absolute() { box(equation) } else { equation }", "equation"))
                driver.write_text(source)
                result = subprocess.run(["typst", "compile", *common, str(driver), str(pdf)],
                                        text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stderr, "")
                with fitz.open(pdf) as doc:
                    pixels.append([page.get_pixmap(matrix=fitz.Matrix(1.5, 1.5)).samples for page in doc])
            self.assertEqual(*pixels)


if __name__ == '__main__':
    unittest.main()
