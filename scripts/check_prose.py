"""Advisory prose check over the Typst sources, using Harper.

Harper parses Typst itself: it skips the markup and everything inside `$…$`,
so it reads the prose and nothing else, and its positions point at the source
line to fix. Running it over the built PDF instead would drag the inline
mathematics back in and bury the signal.

No rule is switched off for convenience. The book's own vocabulary is written
down in `checks/harper-dictionary.txt`: proper names (Cartan, Killing, Weyl),
standard terms of the subject, and the identifiers that appear inside string
arguments. Harper reads those strings as prose — `#idx("Element",
"nilpotent")` reaches it as words — and has no option to skip them, so they
are listed instead (bibliography keys whole). Labels
(`<eq:homomorphism-path-equation>`) it already ignores.

The editor uses the same file through `harper.workspaceDictPath` in
`.vscode/settings.json`, so what Harper says here and what it underlines
while typing are the same thing. That file is also where the disabled rules
and the dialect come from, so the two agree by construction.

Known limitation: the dictionary stops taking
effect as it grows to a few hundred words, and an entry with anything but
plain ASCII letters (`A.`, `Poincaré`) breaks the parse of the whole file, so
such entries are filtered out when the list is generated. Read the other
rules before the spell-check residue.

The check never fails the build. A prose linter is wrong often enough that
blocking an edit on it would cost more than it saves.
"""
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DICTIONARY = ROOT / 'checks' / 'harper-dictionary.txt'
# Keys of references.bib, as in the lint's `bib:` label form.
BIB_KEY = re.compile(r'[A-Z][A-Za-z]*[0-9]{4}[a-z]?')


def editor_settings():
    return json.loads((ROOT / '.vscode/settings.json').read_text())


def disabled_rules():
    """The disabled rules come from the editor settings: one source.

    The VS Code extension reads its own keys (`harper.linters.X`) and passes
    them on to the server, so these are the keys of settings.json; the form
    `harper-ls.linters` is accepted too.
    """
    settings = editor_settings()
    linters = dict(settings.get('harper-ls.linters', {}))
    for key, value in settings.items():
        if key.startswith('harper.linters.'):
            linters[key.rsplit('.', 1)[-1]] = value
    return sorted(name for name, on in linters.items() if not on)


def dialect():
    """The translation is in British spelling (neighbourhood, generalise);
    these are not misspellings."""
    settings = editor_settings()
    return (settings.get('harper.dialect')
            or settings.get('harper-ls.dialect', 'American')).lower()


def lint(paths):
    command = ['harper-cli', 'lint', '--quiet', '--format', 'json',
               '--dialect', dialect()]
    if DICTIONARY.is_file():
        command += ['--user-dict-path', str(DICTIONARY)]
    for rule in disabled_rules():
        command += ['--ignore', rule]
    result = subprocess.run(command + [str(p) for p in paths],
                            capture_output=True, text=True)
    # A note may precede the JSON and a summary line follow it.
    start = result.stdout.find('[')
    if start == -1:
        return []
    return json.JSONDecoder().raw_decode(result.stdout[start:])[0]


def update_dictionary():
    """Add the identifiers of the strings and labels of the sources to the
    dictionary.

    Harper reads string arguments as prose, which is rather useful: a typo
    in a key shows up as an unknown word. A new key has to be added, though,
    or it is unknown as well.
    """
    words = set()
    if DICTIONARY.is_file():
        words |= {line.strip() for line in DICTIONARY.read_text().splitlines()
                  if line.strip()}
    before = len(words)
    for path in sorted((ROOT / 'content').rglob('*.typ')):
        text = path.read_text()
        tokens = re.findall(r'"([^"\n]*)"', text) + re.findall(
            r'<([\w:.-]+)>', text)
        for token in tokens:
            # Harper reads a bibliography key (`Borel1956`) as one word with
            # its digits, so the key is added whole.
            if BIB_KEY.fullmatch(token):
                words.add(token)
                continue
            for word in re.split(r'[^A-Za-z]+', token):
                if len(word) > 1:
                    words.add(word.lower())
    # Harper takes plain words only: one entry with another character, "A."
    # or "Poincaré", breaks the parse of the whole file, and the dictionary
    # silently stops working. Latin letters with the digits of a key are
    # fine (checked with harper-cli 0.60).
    words = {w for w in words
             if re.fullmatch(r'[A-Za-z]+', w) or BIB_KEY.fullmatch(w)}
    DICTIONARY.parent.mkdir(parents=True, exist_ok=True)
    DICTIONARY.write_text('\n'.join(sorted(words, key=str.lower)) + '\n')
    print(f'dictionary: {before} words before, {len(words)} now')


def main():
    if '--update-dictionary' in sys.argv:
        update_dictionary()
        return
    sources = sorted((ROOT / 'content').rglob('*.typ'))
    try:
        report = lint(sources)
    except FileNotFoundError:
        print('harper-cli is not installed; prose check skipped')
        return
    findings = [(item['file'], lint_item)
                for item in report for lint_item in item['lints']]
    for name, item in findings:
        print(f'  {name}:{item["line"]}:{item["column"]}  '
              f'{item["rule"]}: {item["matched_text"]!r} — {item["message"]}')
    kinds = {}
    for _, item in findings:
        kinds[item['rule']] = kinds.get(item['rule'], 0) + 1
    print(f'\nprose: {len(findings)} findings '
          '(advisory, the build does not depend on them)')
    for rule, count in sorted(kinds.items(), key=lambda it: -it[1])[:15]:
        print(f'  {count:4d}  {rule}')


if __name__ == '__main__':
    main()
