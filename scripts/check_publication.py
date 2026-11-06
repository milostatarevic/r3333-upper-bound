#!/usr/bin/env python3
"""Authenticate the selected K60 package and, optionally, both extracted capsules.

This is a passive check. It never builds Lean, generates inputs or runs a solver.
An externally obtained release-index hash is required. --require-cadical refuses
the preparation candidate until the complete second-solver evidence is present.
"""
import argparse
from collections import Counter
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

SCHEMA = 'K60_SELECTED_PUBLICATION_1'
TOTAL = 296081
TOOLS = {'formal_evidence.py', 'native_evidence.py', 'materialize_input.py',
         'publication_formal_evidence.py', 'publication_native_evidence.py',
         'publication_cadical_evidence.py'}
TIMINGS_TOOL = 'publication_timings.py'
TIMINGS_REPORT = 'publication/checks/SUCCESSFUL_RUN_TIMINGS.json'
TIMINGS_SCHEMA = 'K60_SUCCESSFUL_RUN_TIMINGS_1'
MAX_ARCHIVE_PART_BYTES = 2_000_000_000


def require(ok, message):
    if not ok:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read(path):
    return json.loads(Path(path).read_bytes(), object_pairs_hook=unique)


def member(name):
    require(isinstance(name, str) and name and '\\' not in name, 'Invalid member')
    path = PurePosixPath(name)
    require(path.parts and not path.is_absolute() and str(path) == name and
            all(part not in ('.', '..') for part in path.parts), 'Unsafe member: ' + name)
    return path


def pin(path):
    path = Path(path)
    require(path.is_file() and not path.is_symlink() and path == path.resolve(),
            'Expected a canonical regular file: ' + str(path))
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            digest.update(block)
    return {'bytes': path.stat().st_size, 'sha256': digest.hexdigest()}


def archive_pin(record):
    require(isinstance(record, dict) and set(record) == {'bytes', 'sha256'} and
            type(record['bytes']) is int and record['bytes'] > 0 and
            isinstance(record['sha256'], str) and
            re.fullmatch('[0-9a-f]{64}', record['sha256']) is not None,
            'Invalid archive size or SHA256')
    return record


def check_archive_transport(root, label, capsule, catalogue, files, *, archives=True):
    """Bind optional transport parts to the unchanged logical archive bytes."""
    root = Path(root).resolve(strict=True)
    logical = 'archives/k60-' + label + '-evidence.tar.gz'
    expected = archive_pin(capsule['archive_pin'])
    require(capsule['archive'] == logical and catalogue['path'] == logical and
            archive_pin(catalogue['archive']) == expected, 'Wrong capsule archive identity: ' + label)
    declared = {name for name in files if name == logical or name.startswith(logical + '.part')}
    require(('parts' in capsule) == ('parts' in catalogue),
            'Split archive declarations disagree')
    if 'parts' not in capsule:
        require(declared == {logical} and archive_pin(files.get(logical)) == expected,
                'Wrong unsplit archive inventory: ' + label)
        if archives:
            require(pin(root / logical) == expected, 'Changed capsule archive: ' + label)
        return {logical}

    parts = capsule['parts']
    require(isinstance(parts, list) and len(parts) >= 2 and parts == catalogue['parts'],
            'Invalid split archive declaration')
    physical = set()
    for number, part in enumerate(parts, 1):
        require(isinstance(part, dict) and set(part) == {'path', 'bytes', 'sha256'},
                'Invalid archive part record')
        name = logical + f'.part{number:02d}'
        require(part['path'] == name, 'Archive parts are missing, reordered or noncanonical')
        member(name)
        record = archive_pin({key: part[key] for key in ('bytes', 'sha256')})
        # Equality alone would equate integer sizes with booleans/floats.
        catalogue_part = catalogue['parts'][number - 1]
        require(archive_pin({key: catalogue_part[key] for key in ('bytes', 'sha256')}) == record,
                'Wrong archive-index part pin')
        require(record['bytes'] <= MAX_ARCHIVE_PART_BYTES and
                (number == len(parts) or record['bytes'] == MAX_ARCHIVE_PART_BYTES),
                'Wrong archive part size')
        require(archive_pin(files.get(name)) == record,
                'Archive part is absent or has a different indexed pin')
        physical.add(name)
    require(declared == physical, 'Unexpected or missing physical archive file')
    require(sum(part['bytes'] for part in parts) == expected['bytes'],
            'Archive part sizes differ from the logical archive')
    if archives:
        complete = hashlib.sha256()
        total = 0
        for part in parts:
            path = root / part['path']
            require(path.is_file() and not path.is_symlink() and path == path.resolve(),
                    'Expected a canonical regular archive part: ' + str(path))
            digest = hashlib.sha256()
            size = 0
            with path.open('rb') as stream:
                for block in iter(lambda: stream.read(1 << 20), b''):
                    digest.update(block); complete.update(block)
                    size += len(block); total += len(block)
            require(size == part['bytes'] and digest.hexdigest() == part['sha256'],
                    'Changed archive part: ' + part['path'])
        require({'bytes': total, 'sha256': complete.hexdigest()} == expected,
                'Concatenated archive parts differ from the original logical archive')
    return physical


def timing_summary(summary, cases):
    """Validate accounting without treating unsuccessful attempts as coverage."""
    require(isinstance(summary, dict), 'Invalid solver timing summary')
    for name in ('successful_runs', 'unsuccessful_attempts', 'all_attempts'):
        require(type(summary.get(name)) is int and summary[name] >= 0,
                'Invalid solver timing attempt count: ' + name)
    require(summary['successful_runs'] == cases and
            summary['all_attempts'] == cases + summary['unsuccessful_attempts'],
            'Successful timing coverage or attempt accounting mismatch')
    amounts = {}
    for name in ('successful_cpu_seconds', 'unsuccessful_cpu_seconds', 'all_attempt_cpu_seconds'):
        text = summary.get(name)
        require(isinstance(text, str) and re.fullmatch(r'[0-9]+(?:\.[0-9]+)?', text) is not None,
                'Invalid solver CPU decimal: ' + name)
        try:
            value = Decimal(text)
        except InvalidOperation as exc:
            raise ValueError('Invalid solver CPU decimal: ' + name) from exc
        require(value.is_finite() and value >= 0, 'Invalid solver CPU quantity: ' + name)
        amounts[name] = value
    require(amounts['successful_cpu_seconds'] + amounts['unsuccessful_cpu_seconds'] ==
            amounts['all_attempt_cpu_seconds'], 'Solver CPU accounting does not reconcile')
    for prefix in ('successful', 'unsuccessful', 'all_attempt'):
        rounded = format((amounts[prefix + '_cpu_seconds'] / Decimal(3600)).quantize(
            Decimal('0.01'), rounding=ROUND_HALF_UP), 'f')
        require(summary.get(prefix + '_cpu_hours') == rounded, 'Rounded solver CPU hours differ from exact seconds')
    return amounts


def check_successful_run_timings(root, index):
    """Authenticate the complete package's distinct-case timing report."""
    root = Path(root).resolve(strict=True)
    tool_path = 'reproduce/' + TIMINGS_TOOL
    require(TIMINGS_REPORT in index['files'] and tool_path in index['files'] and
            TIMINGS_TOOL in index['tools'], 'Complete publication lacks successful-run timing evidence')
    expected = {'report': TIMINGS_REPORT, 'report_pin': index['files'][TIMINGS_REPORT],
                'tool': tool_path, 'tool_pin': index['tools'][TIMINGS_TOOL],
                'native_manifest_sha256': index['capsules']['native']['manifest_sha256'],
                'selected_ordered_input_sha256': index['selected_ordered_input_sha256']}
    require(index.get('successful_run_timings') == expected,
            'Successful-run timing binding is missing or inconsistent')
    require(pin(root / TIMINGS_REPORT) == expected['report_pin'] and
            pin(root / tool_path) == expected['tool_pin'] == index['files'][tool_path],
            'Changed successful-run timing report or tool')
    report = read(root / TIMINGS_REPORT)
    require(report.get('schema') == TIMINGS_SCHEMA and type(report.get('selected_cases')) is int and
            report['selected_cases'] == TOTAL and
            report.get('native_manifest_sha256') == expected['native_manifest_sha256'] and
            report.get('selected_ordered_input_sha256') == expected['selected_ordered_input_sha256'],
            'Successful-run timings belong to a different capsule or formula census')
    require(isinstance(report.get('policy'), str) and bool(report['policy']), 'Missing solver timing policy')
    require(report.get('timing_tool_sha256') == expected['tool_pin']['sha256'] and
            report.get('existing_all_attempt_fields_changed') is False and
            type(report.get('solver_calls')) is int and report['solver_calls'] == 0,
            'Wrong successful-run timing tool or evidence-preservation claim')
    solvers = report.get('solvers')
    require(isinstance(solvers, dict) and set(solvers) == {'kissat', 'cadical'},
            'Both solvers require successful-run timings')
    totals = {name: timing_summary(summary, TOTAL) for name, summary in solvers.items()}
    for summary in solvers.values():
        require(summary.get('selected_ordered_input_sha256') == expected['selected_ordered_input_sha256'] and
                type(summary.get('direct_c2_successful_runs')) is int and summary['direct_c2_successful_runs'] == 4 and
                all(isinstance(summary.get(field), str) and re.fullmatch('[0-9a-f]{64}', summary[field])
                    for field in ('successful_execution_census_sha256', 'all_attempt_timing_census_sha256')),
                'Wrong successful-run solver census binding')
        statuses = summary.get('recorded_attempt_status_counts')
        require(isinstance(statuses, dict) and set(statuses) <= {'UNSAT', 'TIMEOUT', 'INTERRUPTED', 'ERROR'} and
                all(type(value) is int and value >= 0 for value in statuses.values()) and
                statuses.get('UNSAT') == TOTAL and sum(statuses.values()) == summary['all_attempts'],
                'Raw attempt census differs from solver timing accounting')
    families = report.get('families')
    require(isinstance(families, list) and len(families) == 16 and
            all(isinstance(row, dict) and isinstance(row.get('family'), str) and row['family'] and
                type(row.get('cases')) is int and row['cases'] > 0 for row in families) and
            len({row['family'] for row in families}) == 16 and
            sum(row['cases'] for row in families) == TOTAL, 'Wrong successful-run timing family census')
    for name in solvers:
        parts = [timing_summary(row.get(name), row['cases']) for row in families]
        require(all(sum(part[field] for part in parts) == totals[name][field] for field in totals[name]) and
                all(sum(row[name][field] for row in families) == solvers[name][field]
                    for field in ('successful_runs', 'unsuccessful_attempts', 'all_attempts')),
                'Family solver timing totals do not reconcile')
    return report


def recompute_successful_run_timings(root, index, native_root, native_result):
    report = check_successful_run_timings(root, index)
    sys.path.insert(0, str(Path(root).resolve() / 'reproduce'))
    import publication_timings as timings
    require(pin(Path(timings.__file__).resolve()) == index['tools'][TIMINGS_TOOL],
            'Executing a different successful-run timing tool')
    derived = timings.derive(native_root, index['capsules']['native']['manifest_sha256'],
                             verified_result=native_result)
    require(derived == report, 'Successful-run timing report differs from independently derived native evidence')
    return derived


def check_index(root, expected, *, require_cadical=False, archives=True):
    root = Path(root).resolve(strict=True)
    require(re.fullmatch('[0-9a-f]{64}', expected) is not None, 'External SHA256 is required')
    path = root / 'publication/checks/K60_RELEASE.json'
    require(pin(path)['sha256'] == expected, 'Release-index hash mismatch')
    index = read(path)
    require(index['schema'] == SCHEMA and index['selected_formulas'] == TOTAL and
            index['balance_formulas'] == 7 and index['production_campaign_inputs'] == 296797,
            'Wrong selected publication boundary')
    require(index['kissat_complete'] is True and type(index['cadical_complete']) is bool and
            index['publication_ready'] is index['cadical_complete'], 'Inconsistent completion claims')
    require(index['status'] == ('READY_FOR_HUMAN_REVIEW' if index['cadical_complete'] else
                                'PREPARED_PENDING_CADICAL'), 'Inconsistent publication status')
    if require_cadical:
        require(index['cadical_complete'], 'Full CaDiCaL evidence is still pending')
    expected_tools = TOOLS | ({TIMINGS_TOOL} if index['cadical_complete'] else set())
    require(set(index['tools']) == expected_tools and set(index['capsules']) == {'formal', 'native'},
            'Missing verification tools or capsules')
    require('publication/checks/K60_RELEASE.json' not in index['files'], 'Self-referential index')
    archive_files = set()
    for label, capsule in index['capsules'].items():
        catalogue_path = 'archives/k60-' + label + '-evidence.index.json'
        require(capsule['index'] == catalogue_path and
                pin(root / catalogue_path) == index['files'][catalogue_path], 'Wrong archive-index identity')
        catalogue = read(root / catalogue_path)
        archive_files.update(check_archive_transport(root, label, capsule, catalogue, index['files'],
                                                     archives=archives))
        require(catalogue['manifest']['sha256'] == capsule['manifest_sha256'] and
                catalogue['members'] == len(catalogue['files']), 'Wrong capsule inventory')
        for rel in catalogue['files']:
            member(rel)
    for rel, record in index['files'].items():
        member(rel)
        if rel in archive_files:
            continue  # Checked above in one streaming pass, or explicitly skipped.
        require(pin(root / rel) == record, 'Changed indexed file: ' + rel)
    for name, record in index['tools'].items():
        require(index['files']['reproduce/' + name] == record, 'Wrong verifier pin: ' + name)
    require(index['files']['scripts/check_publication.py'] == pin(Path(__file__).resolve()),
            'Executing a different package checker')
    manifest = read(root / 'formal/SOURCE_MANIFEST.json')
    source = read(root / 'formal/SOURCE_INDEX.json')
    require(len(manifest['modules']) == 1314 and len(manifest['data']) == 110 and
            manifest['roots'] == ['UniformK60.Verification'], 'Wrong formal source boundary')
    require(source['schema'] == 'K60_SELECTED_PUBLIC_SOURCE_INDEX_1' and
            source['source_manifest'] == pin(root / 'formal/SOURCE_MANIFEST.json') and
            source['modules'] == manifest['modules'] and source['embedded_data'] == manifest['data'],
            'Source index differs from selected source manifest')
    expected_sources = {row['path']: {key: row[key] for key in ('sha256', 'bytes')}
                        for row in [*manifest['modules'].values(), *manifest['data'], *manifest['files']]}
    expected_sources['SOURCE_MANIFEST.json'] = pin(root / 'formal/SOURCE_MANIFEST.json')
    for name in ('EmitBase.lean', 'EmitMarkedK60.lean', 'EmitCounters.lean', 'EmitBalanced.lean'):
        expected_sources['reproduce/' + name] = pin(root / 'formal/reproduce' / name)
    require(index['source_files'] == expected_sources, 'Incomplete indexed formal source package')
    for rel, record in expected_sources.items():
        require(index['files']['formal/' + rel] == record == pin(root / 'formal' / rel),
                'Changed public formal source: ' + rel)
    require(source['formal_capsule_manifest_sha256'] == index['capsules']['formal']['manifest_sha256'],
            'Source index points to a different formal capsule')
    if index['cadical_complete']:
        check_successful_run_timings(root, index)
    else:
        require('successful_run_timings' not in index, 'Pending package cannot claim complete solver timings')
    return index


def check_capsules(root, index, formal_root, native_root):
    # The index authentication above checks these exact module bytes first.
    sys.path.insert(0, str(Path(root).resolve() / 'reproduce'))
    import publication_formal_evidence as formal
    import publication_native_evidence as native
    f = formal.verify(formal_root, index['capsules']['formal']['manifest_sha256'])
    n = native.verify(native_root, index['capsules']['native']['manifest_sha256'])
    fm = read(Path(formal_root) / 'FORMAL_PUBLICATION.json')
    nm = read(Path(native_root) / 'NATIVE_RELEASE.json')
    require(f['total_formulas'] == n['total_cases'] == TOTAL and f['passed'] and n['passed'],
            'Formal/native boundary mismatch')
    require(n['full_cadical_campaign_complete'] is index['cadical_complete'],
            'CaDiCaL completion claim differs from evidence')
    require(fm['source_manifest_sha256'] == index['files']['formal/SOURCE_MANIFEST.json']['sha256'],
            'Formal capsule proves a different source package')
    for rel, record in index['source_files'].items():
        require(fm['files']['formal/' + rel] == record == pin(Path(root) / 'formal' / rel),
                'Public formal source differs from capsule: ' + rel)
    store, groups = native.selection(native_root, index['capsules']['native']['manifest_sha256'])
    census = hashlib.sha256(); summaries = {}
    for family in formal.CATALOGUES:
        rows = groups[family].values() if family in ('abd', 'e') else (
            row for row in groups['closure'].values() if row['owner'] in ('C1_ENTRANCE', 'C2_ENTRANCE'))
        counts = Counter((('E_' + row['owner']) if family == 'e' else row['owner'], row['sha256'])
                         for row in rows)
        owners = Counter()
        for (owner, digest), multiplicity in sorted(counts.items()):
            census.update(f'{family} {owner} {digest} {multiplicity}\n'.encode())
            owners[owner] += multiplicity
        summaries[family] = {'cases': sum(counts.values()), 'owners': dict(owners)}
    marked = fm['bindings']['marked']
    require(marked['formula_multiset_sha256'] == census.hexdigest() and
            marked['families'] == summaries and marked['formulas'] ==
            sum(row['cases'] for row in summaries.values()) == TOTAL - 7,
            'Marked native/formal input multiset mismatch')
    direct = {row['id']: row for row in fm['bindings']['balance']['rows']}
    require(set(direct) == {'C2_ROOT_' + o for o in native.OWNERS} |
            {'C1_FIVE_' + o for o in ('UU', 'UT', 'TT')}, 'Wrong seven balance inputs')
    for key, spec in groups['balance'].items():
        require(all(direct[key][field] == spec[field] for field in ('sha256', 'bytes', 'variables', 'clauses')),
                'Direct C2 input-binding mismatch')
    five = {key: row for key, row in groups['closure'].items() if row['owner'].startswith('BALANCE_ALL_FIVE_')}
    require(len(five) == 3, 'Wrong all-five boundary')
    for key, spec in five.items():
        emitted = 'C1_FIVE_' + spec['owner'].removeprefix('BALANCE_ALL_FIVE_')
        require(direct[emitted]['sha256'] == spec['sha256'], 'All-five input-binding mismatch')
    require(n['selected_ordered_input_sha256'] == index['selected_ordered_input_sha256'],
            'Selected formula census differs from release index')
    for label, capsule_root, manifest_name in [('formal', formal_root, 'FORMAL_PUBLICATION.json'),
                                             ('native', native_root, 'NATIVE_RELEASE.json')]:
        catalogue = read(Path(root) / index['capsules'][label]['index'])
        manifest = fm if label == 'formal' else nm
        require(catalogue['files'] == {**manifest['files'], manifest_name: pin(Path(capsule_root) / manifest_name)},
                'Archive inventory differs from accepted capsule: ' + label)
    result = {'formal': f, 'native': n}
    if index['cadical_complete']:
        result['successful_run_timings'] = recompute_successful_run_timings(root, index, native_root, n)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--release-index-sha256', required=True)
    parser.add_argument('--require-cadical', action='store_true')
    parser.add_argument('--skip-archives', action='store_true', help='Authenticate small files before Git LFS retrieval')
    parser.add_argument('--formal-capsule', type=Path)
    parser.add_argument('--native-capsule', type=Path)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    require(bool(args.formal_capsule) == bool(args.native_capsule), 'Supply both extracted capsule paths')
    index = check_index(args.root, args.release_index_sha256,
                        require_cadical=args.require_cadical, archives=not args.skip_archives)
    report = {'passed': True, 'status': index['status'], 'selected_formulas': TOTAL,
              'kissat_complete': True, 'cadical_complete': index['cadical_complete'],
              'archive_bytes_checked': not args.skip_archives, 'solver_calls': 0, 'lean_calls': 0}
    if args.formal_capsule:
        report['capsules'] = check_capsules(args.root, index, args.formal_capsule, args.native_capsule)
    text = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if args.report:
        args.report.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
