#!/usr/bin/env python3
"""Fresh offline verification of the declared mathematical scope.

The paper profile requires all 28 named results, 28 supplementary contracts,
198 equation correspondences and the actual signature/axiom gates. The three
introduction-only external background assertions are excluded by the author
and are never assumed as axioms in the certified proof chain.
"""

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import time
from fetch_dependencies import source_hashes, source_links

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
AXIOM_ENTRY = re.compile(
    r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", re.M)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def require_paper_coverage(inventory, ledger, equation_map):
    """Reject an incomplete paper ledger before expensive build work.

    This is a structural prerequisite. Actual loaded declarations, independent
    signatures, transitive proof closure and kernel axioms are checked later.
    """
    named = [item['id'] for item in inventory['named_statements']]
    supplementary_items = [item for item in inventory['supplementary_claims']
                           if item['id'].startswith('SUP-')]
    supplementary = [item['id'] for item in supplementary_items]
    equations = [item['id'] for item in inventory['equations']]
    require(len(named) == len(set(named)) == 28, 'Incomplete frozen named-result inventory')
    require(set(supplementary) == {f'SUP-{i:02d}' for i in range(1, 29)}
            and len(supplementary) == 28, 'Incomplete frozen supplementary inventory')
    require(len(equations) == len(set(equations)) == 198, 'Incomplete frozen equation inventory')
    require(ledger['full_named_result_coverage'] is True
            and set(ledger['complete_named_results']) == set(named),
            'Paper profile lacks a complete named-result contract')
    require(set(ledger['complete_supplementary_results']) == set(supplementary),
            'Paper profile lacks a complete supplementary contract')
    reviewed = [row['id'] for row in equation_map['equations']]
    require(len(reviewed) == 198 and set(reviewed) == set(equations)
            and equation_map['reviewed_equations'] == 198
            and equation_map['complete'] is True,
            'Paper profile lacks complete reviewed numbered-equation correspondence')
    for item in inventory['named_statements'] + supplementary_items:
        require(item['status'] == 'verified', f'Unverified paper contract: {item["id"]}')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def strip_lean_comments_and_strings(text):
    result, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; i += 2
            elif text.startswith('-/', i):
                depth -= 1; i += 2
            else:
                i += 1
        elif text.startswith('/-', i):
            result.append(' '); depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            result.append(' '); i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            require(i < len(text), 'Unterminated Lean string')
            i += 1
        else:
            result.append(text[i]); i += 1
    require(depth == 0, 'Unterminated Lean block comment')
    return ''.join(result)


def source_snapshot():
    sources = [ROOT/'SharpCut.lean', *sorted((ROOT/'SharpCut').rglob('*.lean')),
               *sorted((ROOT/'audit').glob('*.lean')),
               *sorted((ROOT/'scripts').glob('*.py')),
               *sorted((ROOT/'scripts').glob('*.cjs'))]
    sources += [ROOT/p for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
                                'implementation_map.json', 'paper_inventory.json',
                                'environment/baseline.json', 'plan.json', 'equation_map.json']]
    sources += sorted((ROOT/'vendor/khachiyan').rglob('*.lean'))
    sources += [ROOT/'vendor/khachiyan/PROVENANCE.json', ROOT/'vendor/khachiyan/LICENSE']
    sources += sorted((ROOT/'environment/source-receipts').glob('*.json'))
    sources += [p for p in sorted((ROOT/'paper').rglob('*')) if p.is_file()]
    return {str(p.relative_to(ROOT)): digest(p) for p in sources}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', choices=['kernel-algebra', 'foundations', 'core', 'paper'], required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--require-cold', action='store_true')
    parser.add_argument('--require-project-cold', action='store_true',
                        help='Require a fresh project build while explicitly allowing pinned dependency artifacts')
    parser.add_argument('--toolchain-dir', type=Path)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    require(not output.exists(), f'Refusing to replace an existing verification record: {output}')
    output.mkdir(parents=True)
    record = {'started_utc': datetime.now(timezone.utc).isoformat(),
              'profile': args.profile, 'require_cold': args.require_cold,
              'scope': 'Verification of the declared paper-results mathematical scope.',
              'commands': [], 'success': False, 'full_paper_verified': False, 'network_requests': 0}

    def save():
        (output/'run.json').write_text(json.dumps(record, indent=2)+'\n')

    environment = os.environ.copy()
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'ELAN_TOOLCHAIN', 'LAKE_HOME']:
        environment.pop(key, None)
    environment.update(MATHLIB_NO_CACHE_ON_UPDATE='1', GIT_TERMINAL_PROMPT='0')

    def run(label, command):
        started = time.monotonic()
        path = output/(label+'.log')
        record['running_command'] = label
        save()
        with path.open('w') as log:
            result = subprocess.run([str(x) for x in command], cwd=ROOT, env=environment,
                                    stdout=log, stderr=subprocess.STDOUT, text=True)
        record.pop('running_command', None)
        record['commands'].append({'label': label, 'command': [str(x) for x in command],
                                   'exit_code': result.returncode, 'log': path.name,
                                   'sha256': digest(path), 'seconds': round(time.monotonic()-started, 3)})
        save()
        require(result.returncode == 0, f'{label} failed; see {path}')
        print(f'PASS {label}', flush=True)
        return path.read_text()

    try:
        save()
        if args.profile == 'paper':
            require_paper_coverage(json.loads((ROOT/'paper_inventory.json').read_text()),
                                   json.loads((ROOT/'implementation_map.json').read_text()),
                                   json.loads((ROOT/'equation_map.json').read_text()))
        pin = (ROOT/'lean-toolchain').read_text().strip()
        require(pin == 'leanprover/lean4:v4.35.0-rc2', 'Toolchain pin drift')
        toolchain = args.toolchain_dir or Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0-rc2'
        lean, lake = toolchain/'bin/lean', toolchain/'bin/lake'
        require(lean.is_file() and lake.is_file(), 'Pinned toolchain is not installed')
        manifest = json.loads((ROOT/'lake-manifest.json').read_text())
        baseline = json.loads((ROOT/'environment/baseline.json').read_text())
        require(manifest['name'] == 'sharpCut', 'Incorrect project name')
        packages = {p['name']: p for p in manifest['packages']}
        require(set(packages) == {p['name'] for p in baseline['packages']}, 'Incomplete dependency manifest')
        record['dependency_revisions'] = {}
        for pin in baseline['packages']:
            name, revision = pin['name'], pin['rev']
            package = packages[name]
            require(package['type'] == 'path' and package.get('sourceRevision') == revision,
                    f'Unpinned or unsupported package source: {name}')
            directory = (ROOT/package['dir']).resolve()
            require(directory.is_relative_to(ROOT) and directory.is_dir(), f'External/missing package: {name}')
            receipt = json.loads((ROOT/package['sourceReceipt']).read_text())
            require(receipt['revision'] == revision and receipt['files'] == source_hashes(directory)
                    and receipt.get('symlinks', {}) == source_links(directory), f'Dependency source changed: {name}')
            record['dependency_revisions'][name] = revision
        provenance = json.loads((ROOT/'vendor/khachiyan/PROVENANCE.json').read_text())
        require(provenance['source_commit'] == baseline['legacy_source_commit'], 'Legacy source pin drift')
        for name, expected in provenance['file_sha256'].items():
            require(digest(ROOT/'vendor/khachiyan'/name) == expected, f'Legacy source changed: {name}')
        config = strip_lean_comments_and_strings((ROOT/'lakefile.lean').read_text())
        require(not re.search(r'\bpost_update\b|\bfrom\s+git\b', config), 'Unexpected root acquisition hook')
        record['sources'] = source_snapshot()
        compiled = [str(p.relative_to(ROOT)) for p in (ROOT/'.lake').rglob('*')
                    if p.is_file() and p.suffix in {'.olean', '.ilean'}]
        record['preexisting_compiled_artifact_count'] = len(compiled)
        require(not args.require_cold or not compiled, 'Cold reproduction contains preexisting Lean artifacts')
        project_compiled = [p for p in (ROOT/'.lake/build').rglob('*')
                            if p.is_file() and p.suffix in {'.olean', '.ilean'}]
        record['preexisting_project_compiled_artifact_count'] = len(project_compiled)
        require(not args.require_project_cold or not project_compiled,
                'Project-cold reproduction contains preexisting project artifacts')
        for path in [ROOT/'SharpCut.lean', *sorted((ROOT/'SharpCut').rglob('*.lean')),
                     *sorted((ROOT/'vendor/khachiyan').rglob('*.lean'))]:
            code = strip_lean_comments_and_strings(path.read_text())
            require(not re.search(r'\b(sorry|sorryAx|axiom|native_decide|ofReduceBool)\b', code),
                    f'Forbidden proof token in {path}')
        version = run('lean-version', [lean, '--version'])
        require('4.35.0-rc2' in version and '11acb17ec6b07a8f9e9173e6845197929540936b' in version,
                'Actual compiler version drift')
        run('lake-version', [lake, '--version'])
        search = run('lean-path', [lake, '--no-cache', 'env', 'printenv', 'LEAN_PATH'])
        for item in search.strip().split(os.pathsep):
            path = (ROOT/item).resolve()
            require(path.is_relative_to(ROOT) or path.is_relative_to(toolchain.resolve()),
                    f'Unapproved import path: {path}')
        run('build', [lake, '--no-cache', '--rehash', '--no-ansi', 'build'])
        listing = run('enumerate', [lake, '--no-cache', 'env', 'lean', 'audit/Enumerate.lean'])
        names = re.findall(r'^SHARPCUT_DECL (\S+)$', listing, re.M)
        require(names and names == sorted(set(names)), 'Empty, duplicate or unordered declaration audit')
        require('SHARPCUT_CLOSURE_PASS' in listing, 'Missing actual proof-closure traversal')
        ledger = json.loads((ROOT/'implementation_map.json').read_text())
        public = [n for n in names if not re.search(r'\._proof_\d+(?:_\d+)*$', n)]
        require(public == sorted(item['declaration'] for item in ledger['supporting_declarations']),
                'Actual declarations do not match the implementation coverage ledger')
        modules = re.findall(r'^SHARPCUT_MODULE (\S+)$', listing, re.M)
        expected_modules = ['SharpCut'] + [str(p.relative_to(ROOT)).removesuffix('.lean').replace('/', '.')
                                          for p in sorted((ROOT/'SharpCut').rglob('*.lean'))]
        require(sorted(modules) == sorted(expected_modules), 'Certified project import closure mismatch')
        legacy = re.findall(r'^LEGACY_DECL (\S+)$', listing, re.M)
        require(legacy and legacy == sorted(set(legacy)), 'Empty or inconsistent legacy audit')
        legacy_modules = re.findall(r'^LEGACY_MODULE (\S+)$', listing, re.M)
        allowed_legacy = {name.removesuffix('.lean').replace('/', '.') for name in provenance['file_sha256']}
        require(set(legacy_modules) <= allowed_legacy, 'Unexpected legacy import source')
        all_names = names + legacy
        source = output/'Axioms.lean'
        source.write_text('import SharpCut\n\n' + '\n'.join('#print axioms '+n for n in all_names)+'\n')
        axioms = run('axioms', [lake, '--no-cache', 'env', 'lean', source])
        entries = AXIOM_ENTRY.findall(axioms)
        require([n for n, _ in entries] == all_names, 'Fresh axiom output order/count mismatch')
        for name, values in entries:
            used = {v.strip() for v in values.split(',') if v.strip()}
            require(used <= ALLOWED_AXIOMS, f'Forbidden axioms for {name}: {used-ALLOWED_AXIOMS}')
        signatures = run('statements', [lake, '--no-cache', 'env', 'lean', 'audit/Statements.lean'])
        require('SHARPCUT_STATEMENTS_PASS' in signatures, 'Missing explicit statement comparison')
        require('SHARPCUT_GEOMETRY_STATEMENTS_PASS' in signatures, 'Missing geometry/certificate signature comparison')
        inventory = json.loads((ROOT/'paper_inventory.json').read_text())
        complete = ledger.get('complete_named_results', {})
        require(set(complete) <= {'lem-certificate', 'lem-rational', 'lem-john', 'lem-reduction', 'lem-lifted-bound', 'lem-hermite', 'lem-moments', 'lem-variational', 'prop-dim3', 'thm-determinant', 'thm-frame-bound', 'thm-sharp', 'prop-gap', 'lem-matching', 'thm-equality', 'prop-extremizers', 'prop-gap-control', 'lem-residual', 'lem-local', 'lem-geometric-control', 'thm-stability', 'prop-exact-duality', 'prop-kkt', 'lem-cauchy', 'lem-cauchy-minus', 'lem-inverse-trace', 'prop-polar', 'cor-iteration'},
                'Named result lacks a separately audited full contract')
        require(ledger.get('full_named_result_coverage', False) == (set(complete) == {item['id'] for item in inventory['named_statements']}), 'Named coverage flag disagrees with actual complete IDs')
        for label, declarations in complete.items():
            require(declarations and all(name in names for name in declarations), f'Missing named theorem: {label}')
        require('SHARPCUT_SCALAR_STATEMENTS_PASS' in signatures, 'Missing original scalar-integral contract')
        require('SHARPCUT_JOHN_STATEMENTS_PASS' in signatures, 'Missing full John contact contract')
        require('SHARPCUT_REDUCTION_STATEMENTS_PASS' in signatures, 'Missing actual finite reduction contract')
        require('SHARPCUT_LIFTED_BOUND_STATEMENTS_PASS' in signatures, 'Missing full lifted-gain contract')
        require('SHARPCUT_HERMITE_STATEMENTS_PASS' in signatures, 'Missing exact Hermite/loss contracts')
        require('SHARPCUT_BLOCK_DIMENSION_TWO_STATEMENTS_PASS' in signatures, 'Missing full block and dimension-two contracts')
        require('SHARPCUT_DIRECT_COUPLING_STATEMENTS_PASS' in signatures, 'Missing direct coupling and endpoint contracts')
        require('SHARPCUT_FULL_FRAME_GEOMETRIC_UPPER_STATEMENTS_PASS' in signatures, 'Missing all-dimensional frame/equality and actual geometric upper contracts')
        require('SHARPCUT_CORE_SHARP_STATEMENTS_PASS' in signatures, 'Missing complete sharp geometry/attainment/supremum contracts')
        require('SHARPCUT_GAP_MATCHING_EQUALITY_STATEMENTS_PASS' in signatures, 'Missing full gap/affine-volume/matching/equality/extremizer contracts')
        require('SHARPCUT_SUPPLEMENTARY_FOUNDATIONS_STATEMENTS_PASS' in signatures, 'Missing reused geometry/polar/gap/factorization contracts')
        require('SHARPCUT_GEOMETRIC_RESIDUAL_STATEMENTS_PASS' in signatures, 'Missing exact residual/norm/global-distance contracts')
        require('SHARPCUT_LOCAL_GEOMETRIC_COERCIVITY_STATEMENTS_PASS' in signatures, 'Missing exact local coercivity, threshold and contact stability contracts')
        require('SHARPCUT_CENTER_SUPPORT_TRANSFER_STATEMENTS_PASS' in signatures, 'Missing exact support/center/isotropic norm contracts')
        require('SHARPCUT_FULL_STABILITY_STATEMENTS_PASS' in signatures, 'Missing all five exact stability bounds and ordered supplementary transfers')
        require('SHARPCUT_EXACT_DUALITY_KKT_STATEMENTS_PASS' in signatures, 'Missing actual attained duality and full KKT/moment contracts')
        require('SHARPCUT_GENERAL_CAUCHY_STATEMENTS_PASS' in signatures, 'Missing all transverse matrix/vector Cauchy and exact contact contracts')
        require('SHARPCUT_COMPLEMENTARY_CAUCHY_STATEMENTS_PASS' in signatures, 'Missing full complementary transverse Cauchy, contact and endpoint contracts')
        require('SHARPCUT_INVERSE_TRACE_STATEMENTS_PASS' in signatures, 'Missing both all-test inverse-trace equivalences, strict positivity and attaining test contracts')
        require('SHARPCUT_COMMON_POLAR_STATEMENTS_PASS' in signatures, 'Missing actual common contraction upper/attainment, skew Gram and Loewner contracts')
        require('SHARPCUT_ITERATION_STATEMENTS_PASS' in signatures, 'Missing actual sharp iteration, positive finite volume/ball and logarithmic-domain contracts')
        require('SHARPCUT_ENDPOINT_SUPPLEMENTARY_STATEMENTS_PASS' in signatures, 'Missing exact endpoint integral/log/rational supplementary contracts')
        require('SHARPCUT_LORENTZ_SUPPLEMENTARY_STATEMENTS_PASS' in signatures, 'Missing exact homogeneous Lorentz, model matching and full weight/zero-defect supplementary contracts')
        require('SHARPCUT_RELATIVE_VOLUME_STOPPING_STATEMENTS_PASS' in signatures, 'Missing physical optimum volume and feasible gap stopping contract')
        require('SHARPCUT_ROUNDING_INITIALIZATION_STATEMENTS_PASS' in signatures, 'Missing actual arbitrary-center symmetric/general John rounding and explicit next-cut initialization contracts')
        require('SHARPCUT_OFFSET_MULTIPLE_DUAL_STATEMENTS_PASS' in signatures, 'Missing actual full-dimensional offset/multiple dual and changed normalization/balance contracts')
        require('SHARPCUT_CONVEX_LORENTZ_STATEMENTS_PASS' in signatures, 'Missing full all-matrix logdet concavity, convex SOC support/feasibility and Lorentz self-duality contracts')
        require('SHARPCUT_LOW_DIMENSION_REMAINDER_STATEMENTS_PASS' in signatures, 'Missing original low-dimensional reciprocal/integral/exact remainder contracts')
        require('SHARPCUT_LEGACY_CONE_STATEMENTS_PASS' in signatures, 'Missing rebuilt actual legacy cone/fixed-dimensional maximality and one-dimensional volume contracts')
        require('SHARPCUT_INSTANCE_DUAL_STATEMENTS_PASS' in signatures, 'Missing actual instance/fixed-weight determinant maxima, attained frame infimum and physical volume contracts')
        require('SHARPCUT_UNNORMALIZED_LAGRANGIAN_STATEMENTS_PASS' in signatures, 'Missing full raw EReal Lagrangian conjugate/infinite cases, exact scale, actual strict seed and attained unnormalized dual contracts')
        require('SHARPCUT_CONSTANT_SERIES_ASYMPTOTICS_STATEMENTS_PASS' in signatures, 'Missing full positive-dimensional monotonicity/bounds/limit, absolute logarithmic series and genuine O(n^-4) contracts')
        require('SHARPCUT_NUCLEAR_DEFICIT_STATEMENTS_PASS' in signatures, 'Missing all-matrix nuclear triangle/rank-one/trace and singular-value contracts, full four-term deficit and commuting polar correction')
        require('SHARPCUT_SIGNED_PYRAMID_STATEMENTS_PASS' in signatures, 'Missing full signed transverse family, literal square-pyramid/frustum geometry, exact vertices/facets/contacts and actual John-volume contracts')
        require('SHARPCUT_REGULAR_SIMPLEX_MODEL_STATEMENTS_PASS' in signatures, 'Missing constructive all-positive-dimensional regular simplex, exact model supports, actual Figure 1 ellipse/area and ordinary half-ball Lebesgue volume contracts')
        require('SHARPCUT_AFFINE_SIMPLEX_STATEMENTS_PASS' in signatures, 'Missing arbitrary all-positive-dimensional affine-simplex actual John center/shape/covariance/volume and general polar transport contracts')
        supplementary = ledger.get('complete_supplementary_results', {})
        external = ledger.get('complete_external_results', {})
        require(set(external) <= {f'EXT-{i:02d}' for i in range(1, 5)},
                'Unknown external mathematical assertion')
        for label, declarations in external.items():
            require(declarations and all(name in all_names for name in declarations),
                    f'Missing rooted external theorem: {label}')
        if 'EXT-04' in external:
            require('SHARPCUT_REUSED_UNIFORM_EXTERNAL_PASS' in signatures,
                    'Missing independent inherited uniform-bound/optimality contracts')
        require(set(supplementary) <= {'SUP-01', 'SUP-06', 'SUP-07', 'SUP-13', 'SUP-14', 'SUP-15', 'SUP-16', 'SUP-19', 'SUP-20', 'SUP-28', 'SUP-21', 'SUP-24', 'SUP-17', 'SUP-05', 'SUP-03', 'SUP-10', 'SUP-11', 'SUP-26', 'SUP-02', 'SUP-18', 'SUP-27', 'SUP-12', 'SUP-22', 'SUP-09', 'SUP-23', 'SUP-08', 'SUP-04', 'SUP-25'},
                'Supplementary claim lacks a reviewed complete contract')
        for label, declarations in supplementary.items():
            require(declarations and all(name in all_names for name in declarations), f'Missing supplementary declaration: {label}')
        require('SHARPCUT_SELECTED_VARIATIONAL_EQUATION_PASS' in signatures,
                'Missing exact selected variational value contract')
        require('SHARPCUT_DETERMINANT_EQUATION_CHAINS_PASS' in signatures,
                'Missing literal theta and determinant elimination intermediate contracts')
        require('SHARPCUT_GAP_EQUATION_CHAINS_PASS' in signatures,
                'Missing literal gap/equality/initialization intermediate contracts')
        require('SHARPCUT_INITIAL_EQUATION_CHAINS_PASS' in signatures,
                'Missing exact initial numbered-equation trace/mean/radius contracts')
        equation_map = json.loads((ROOT/'equation_map.json').read_text())
        expected_equations = {item['id']: item for item in inventory['equations']}
        reviewed_rows = equation_map['equations']
        reviewed_ids = {row['id'] for row in reviewed_rows}
        require(len(reviewed_ids) == len(reviewed_rows), 'Duplicate numbered-equation correspondence')
        require(reviewed_ids <= set(expected_equations), 'Unexpected numbered-equation correspondence')
        require(equation_map['reviewed_equations'] == len(reviewed_rows), 'Equation review count disagrees with actual rows')
        require(equation_map['complete'] == (reviewed_ids == set(expected_equations)), 'Equation completeness flag drift')
        for row in reviewed_rows:
            expected = expected_equations[row['id']]
            require(row['coverage_owner'] == expected['coverage_owner'] and row['formula_sha256'] == expected['sha256'],
                    f'Equation baseline/owner drift: {row["id"]}')
            require(row['status'] == 'reviewed_correspondence' and row['correspondence'].strip(),
                    f'Equation lacks reviewed mathematical correspondence: {row["id"]}')
            require(row['declarations'] and all(name in all_names for name in row['declarations']),
                    f'Equation references an unloaded declaration: {row["id"]}')
        record.update(numbered_equation_correspondences_reviewed=len(reviewed_rows),
                      numbered_equations_total=len(expected_equations),
                      numbered_equation_map_complete=equation_map['complete'])
        if args.profile == 'core':
            required_core = {'lem-certificate', 'lem-john', 'lem-reduction', 'thm-sharp',
                             'thm-frame-bound', 'thm-determinant', 'prop-dim3'}
            require(required_core <= set(complete), 'Missing complete named result in the core proof chain')
            record['scope'] = 'Complete core sharp geometry, all-dimensional determinant chain, fixed-dimensional attainment and actual-volume suprema; full paper incomplete.'
        if args.profile == 'paper':
            require_paper_coverage(inventory, ledger, equation_map)
            record['scope'] = ('Complete paper-results profile: 28 named results, 28 supplementary '
                               'contracts, all 198 numbered-equation correspondences, actual '
                               'Euclidean/maximal-Lebesgue-volume geometry and every supporting '
                               'signature/axiom gate. Cited EXT centroid and algorithm-cost '
                               'survey assertions are outside this profile.')
            record['external_survey_assertions_included'] = False
        for item in inventory['named_statements']:
            if item['status'] == 'verified':
                require(item['id'] in complete and item['lean_declarations'] == complete[item['id']],
                        f'Paper result marked verified outside accepted scope: {item["id"]}')
        for item in inventory['supplementary_claims']:
            if item['status'] == 'verified':
                accepted = external if item['id'].startswith('EXT-') else supplementary
                require(item['id'] in accepted and item['lean_declarations'] == accepted[item['id']],
                        f'Supplementary claim marked verified outside accepted scope: {item["id"]}')
        for pin in baseline['packages']:
            package = packages[pin['name']]
            receipt = json.loads((ROOT/package['sourceReceipt']).read_text())
            require(receipt['files'] == source_hashes(ROOT/package['dir'])
                    and receipt.get('symlinks', {}) == source_links(ROOT/package['dir']),
                    f'Dependency source changed during build: {pin["name"]}')
        require(source_snapshot() == record['sources'], 'Sources or pins changed during verification')
        record.update(success=True, core_verified=args.profile in {'core', 'paper'},
                      full_paper_verified=args.profile == 'paper',
                      paper_results_verified=args.profile == 'paper',
                      all_mathematical_assertions_verified=False,
                      public_declarations=len(public), audit_entries=len(entries),
                      named_paper_results_verified=len(complete), complete_named_results=complete,
                      supplementary_results_verified=len(supplementary), complete_supplementary_results=supplementary,
                      external_results_verified=len(external), complete_external_results=external,
                      deferred_external_results=[item['id'] for item in inventory['supplementary_claims']
                                                 if item['id'].startswith('EXT-') and item['id'] not in external and item['status'] != 'excluded_background'],
                      excluded_background_results=[item['id'] for item in inventory['supplementary_claims']
                                                   if item['status'] == 'excluded_background'],
                      project_modules=modules, legacy_modules=legacy_modules,
                      project_audit_entries=len(names), legacy_audit_entries=len(legacy),
                      axiom_sets={n: [v.strip() for v in a.split(',') if v.strip()] for n, a in entries})
    except Exception as error:
        record['error'] = str(error)
        print(f'FAIL: {error}', flush=True)
    finally:
        record['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    return 0 if record['success'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
