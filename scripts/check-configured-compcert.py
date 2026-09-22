#!/usr/bin/env python3
"""Build the explicit CompCert configuration and kernel-check the assembly certificates.

Inputs: --compcert-root, --clight-source, --work-dir, --jobs. Output: the --output JSON record
(the retained run is evidence/assembly-certificate.json) and check.log in the work directory.
Requires a built CompCert 3.17 x86_64 tree at the pinned revision, used read-only as the origin
of the source archive, Docker with the pinned Coq image, and compcert/certification/. Every proof
object, including the hash-checked generated parser, is rebuilt in the new work directory.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True

PROOFS = [
    'ClightExample', 'ClightRules', 'ClightDeterminism', 'ClightSafety',
    'CsharpminorExample', 'CminorExample', 'ClightLibrary', 'AnnotatedBehavior',
    'ClightApplication', 'CminorApplication', 'CompilerBackend', 'AsmApplication',
    'ValueAccuracy', 'ExampleIntegral', 'ApplicationAccuracy', 'InternalCosine',
    'PolynomialApplication', 'PolynomialCompilation', 'FiniteArithmetic',
    'StoredRules', 'RuleLibrary', 'PolynomialRules', 'StoredPolynomialRules',
    'PolynomialRulesAccuracy', 'StoredPolynomialAccuracy',
    'PolynomialRulesCompilation', 'StoredPolynomialCompilation',
]
CERTIFICATES = [
    'CertifiedPolynomial', 'CertifiedExternal', 'CertifiedPolynomialRules',
    'CertifiedStoredPolynomial',
]
AUDITED = [
    'FiniteArithmetic.Binary64Roundoff.epsilon_nonnegative',
    'FiniteArithmetic.Binary64Roundoff.round_bounded',
    'FiniteArithmetic.Binary64Roundoff.round_no_overflow',
    'FiniteArithmetic.Binary64Roundoff.add_bounded',
    'FiniteArithmetic.Binary64Roundoff.mul_bounded',
    'FiniteArithmetic.Binary64Roundoff.product_mass_nonnegative',
    'FiniteArithmetic.Binary64Roundoff.integrate_bounded',
    'RuleLibrary.RuleLibrary.load_float_table_nth',
    'RuleLibrary.RuleLibrary.point_table_load',
    'RuleLibrary.RuleLibrary.weight_table_load',
    'RuleLibrary.RuleLibrary.gauss_point_execution',
    'RuleLibrary.RuleLibrary.gauss_weight_execution',
    'RuleLibrary.RuleLibrary.integrate_rule_execution',
    'RuleLibrary.RuleLibrary.integrate_rule_steps',
    'StoredRules.stored_terms_length',
    'StoredRules.stored_terms_rule_order',
    'StoredRules.stored_value_rule_order',
    'RuleLibrary.RuleLibrary.stored_gauss_point_execution',
    'RuleLibrary.RuleLibrary.stored_gauss_weight_execution',
    'RuleLibrary.RuleLibrary.stored_integrate_execution',
    'RuleLibrary.RuleLibrary.stored_integrate_steps',
    'PolynomialRules.program_main_found',
    'PolynomialRules.application_initializes',
    'PolynomialRules.initial_memory_exists',
    'PolynomialRules.testfun_execution',
    'PolynomialRules.library_execution',
    'PolynomialRules.main_execution',
    'PolynomialRules.main_initial_state',
    'PolynomialRules.main_steps',
    'PolynomialRules.application_terminates',
    'PolynomialRules.application_all_behaviors',
    'PolynomialRulesAccuracy.result_value_bits',
    'PolynomialRulesAccuracy.result_value_real',
    'PolynomialRulesAccuracy.result_value_finite',
    'PolynomialRulesAccuracy.sin_one_tight_enclosure',
    'PolynomialRulesAccuracy.result_value_accuracy',
    'PolynomialRulesAccuracy.result_integral_accuracy',
    'PolynomialRulesAccuracy.result_behavior_accurate',
    'PolynomialRulesAccuracy.source_application_accuracy',
    'PolynomialRulesCompilation.first_translation_succeeds',
    'PolynomialRulesCompilation.second_translation_succeeds',
    'PolynomialRulesCompilation.first_program_translation',
    'PolynomialRulesCompilation.second_program_translation',
    'PolynomialRulesCompilation.application_forward_simulation',
    'PolynomialRulesCompilation.application_terminates',
    'PolynomialRulesCompilation.application_all_behaviors',
    'PolynomialRulesCompilation.cminor_application_accuracy',
    'PolynomialRulesCompilation.assembly_forward_simulation',
    'PolynomialRulesCompilation.assembly_terminates',
    'PolynomialRulesCompilation.assembly_all_behaviors',
    'PolynomialRulesCompilation.assembly_application_accuracy',
    'StoredPolynomialRules.application_initializes',
    'StoredPolynomialRules.initial_memory_exists',
    'StoredPolynomialRules.testfun_execution',
    'StoredPolynomialRules.library_execution',
    'StoredPolynomialRules.main_execution',
    'StoredPolynomialRules.main_initial_state',
    'StoredPolynomialRules.main_steps',
    'StoredPolynomialRules.application_terminates',
    'StoredPolynomialRules.application_all_behaviors',
    'StoredPolynomialRules.application_rule_order',
    'StoredPolynomialRules.result_value_rule_order',
    'StoredPolynomialRules.result_trace_rule_order',
    'StoredPolynomialAccuracy.result_value_bits',
    'StoredPolynomialAccuracy.result_value_real',
    'StoredPolynomialAccuracy.result_value_finite',
    'StoredPolynomialAccuracy.sin_one_decimal_enclosure',
    'StoredPolynomialAccuracy.result_value_accuracy',
    'StoredPolynomialAccuracy.result_integral_accuracy',
    'StoredPolynomialAccuracy.result_behavior_accurate',
    'StoredPolynomialAccuracy.source_application_accuracy',
    'StoredPolynomialCompilation.first_translation_succeeds',
    'StoredPolynomialCompilation.second_translation_succeeds',
    'StoredPolynomialCompilation.first_program_translation',
    'StoredPolynomialCompilation.second_program_translation',
    'StoredPolynomialCompilation.application_forward_simulation',
    'StoredPolynomialCompilation.application_terminates',
    'StoredPolynomialCompilation.application_all_behaviors',
    'StoredPolynomialCompilation.cminor_application_accuracy',
    'StoredPolynomialCompilation.assembly_forward_simulation',
    'StoredPolynomialCompilation.assembly_terminates',
    'StoredPolynomialCompilation.assembly_all_behaviors',
    'StoredPolynomialCompilation.assembly_application_accuracy',
    'CertifiedPolynomial.backend_succeeds',
    'CertifiedPolynomial.concrete_cminor_eq',
    'CertifiedPolynomial.compiled',
    'CertifiedPolynomial.application_terminates',
    'CertifiedPolynomial.application_all_behaviors',
    'CertifiedPolynomial.application_accuracy',
    'CertifiedExternal.backend_succeeds',
    'CertifiedExternal.concrete_cminor_eq',
    'CertifiedExternal.compiled',
    'CertifiedExternal.application_terminates',
    'CertifiedExternal.application_all_behaviors',
    'CertifiedExternal.application_accuracy',
    'CertifiedPolynomialRules.backend_succeeds',
    'CertifiedPolynomialRules.concrete_cminor_eq',
    'CertifiedPolynomialRules.compiled',
    'CertifiedPolynomialRules.application_terminates',
    'CertifiedPolynomialRules.application_all_behaviors',
    'CertifiedPolynomialRules.application_accuracy',
    'CertifiedStoredPolynomial.backend_succeeds',
    'CertifiedStoredPolynomial.concrete_cminor_eq',
    'CertifiedStoredPolynomial.compiled',
    'CertifiedStoredPolynomial.application_terminates',
    'CertifiedStoredPolynomial.application_all_behaviors',
    'CertifiedStoredPolynomial.application_accuracy',
]
BIN = '/home/coq/.opam/4.13.1+flambda/bin/'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def capture(command):
    return subprocess.check_output(command, text=True).strip()


def logged(command, path):
    print(f'Checking {path.name}', flush=True)
    with path.open('w') as out:
        result = subprocess.run(command, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode:
        print(path.read_text()[-12000:])
        raise subprocess.CalledProcessError(result.returncode, command)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compcert-root', required=True, type=Path)
    parser.add_argument('--work-dir', required=True, type=Path)
    parser.add_argument('--clight-source', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--jobs', type=int, default=8)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    checker_sha256 = digest(Path(__file__))
    baseline_sha256 = digest(repo / 'scripts/check-clight.py')
    spec = importlib.util.spec_from_file_location('baseline', repo / 'scripts/check-clight.py')
    baseline = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(baseline)
    bundle = repo / 'compcert/certification'
    manifest = json.loads((bundle / 'configuration-files.json').read_text())
    source = args.compcert_root.resolve(strict=True)
    work = args.work_dir.resolve()
    if work.is_relative_to(source) or work.is_relative_to(repo):
        raise ValueError('Use a new build directory outside both source trees.')
    if work.exists() and any(work.iterdir()):
        raise ValueError('The build directory must be empty; no existing files are removed.')
    if args.jobs < 1:
        raise ValueError('--jobs must be positive.')
    revision = capture(['git', '-C', str(source), 'rev-parse', 'HEAD'])
    if revision != baseline.COMPCERT_REVISION or revision != manifest['base_revision']:
        raise ValueError('Unexpected CompCert base revision.')
    if digest(source / 'cparser/Parser.v') != manifest['generated_parser_sha256']:
        raise ValueError('Unexpected generated parser source.')
    if digest(bundle / 'Makefile.config') != manifest['makefile_config_sha256']:
        raise ValueError('Unexpected compiler build configuration.')
    if digest(args.clight_source) != baseline.CLIGHT_SHA256:
        raise ValueError('Unexpected generated Clight source.')
    work.mkdir(parents=True, exist_ok=True)
    root = work / 'compiler'
    root.mkdir()
    archive = work / 'compcert-source.tar'
    with archive.open('wb') as out:
        subprocess.run(['git', '-C', str(source), 'archive', revision], stdout=out, check=True)
    with tarfile.open(archive) as tar:
        tar.extractall(root, filter='data')
    shutil.copyfile(source / 'cparser/Parser.v', root / 'cparser/Parser.v')
    shutil.copyfile(bundle / 'Makefile.config', root / 'Makefile.config')
    (work / 'proof').mkdir()
    (work / 'export').mkdir()
    shutil.copyfile(args.clight_source, work / 'proof/quadrules.v')
    for name in ['Ctypesdefs.v', 'Clightdefs.v']:
        shutil.copyfile(root / 'export' / name, work / 'export' / name)
    for name in PROOFS + CERTIFICATES:
        src = repo / 'compcert' / f'{name}.v'
        if name in CERTIFICATES:
            src = bundle / f'{name}.v'
        text = src.read_text()
        if re.search(r'\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters|Abort|native_compute)\b', text):
            raise ValueError(f'Unproved declarations or unchecked computation in {src}.')
        (work / 'proof' / src.name).write_text(text)
    audit_source = ('From QuadratureC Require Import ' +
                    ' '.join(PROOFS + CERTIFICATES) + '.\n')
    audit_source += ''.join(f'Print Assumptions {name}.\n' for name in AUDITED)
    (work / 'proof/ConfiguredAudit.v').write_text(audit_source)
    common = [
        'docker', 'run', '--rm', '--read-only', '--network', 'none',
        '--tmpfs', '/tmp:rw,size=512m',
        '--user', f'{os.getuid()}:{os.getgid()}',
        '-e', f'PATH={BIN}:/usr/local/bin:/usr/bin:/bin',
        '-v', f'{work}:/work', '-w', '/compcert',
    ]
    def docker(command, writable=False):
        return common + ['-v', f'{root}:/compcert' + ('' if writable else ':ro'),
                         '--entrypoint', command[0], baseline.IMAGE] + command[1:]
    coq_version = capture(docker([baseline.COQC, '--version']))
    make = ['/usr/bin/make', f'-j{args.jobs}', f'COQBIN={BIN}']
    logged(docker(make + ['depend'], True), work / 'generate-original.log')
    for name, hashes in manifest['files'].items():
        if digest(root / name) != hashes['before']:
            raise ValueError(f'Unexpected original source: {name}')
    patch = bundle / 'configuration.patch'
    with patch.open() as src:
        subprocess.run(['git', 'apply', '-'], cwd=root, stdin=src, check=True)
    for name, hashes in manifest['files'].items():
        if digest(root / name) != hashes['after']:
            raise ValueError(f'Unexpected configured source: {name}')
    logged(docker(make + ['depend'], True), work / 'dependencies.log')
    logged(docker(make + ['proof'], True), work / 'compiler-proof.log')
    for name, hashes in manifest['files'].items():
        if digest(root / name) != hashes['after']:
            raise ValueError(f'Generated source changed after checking: {name}')
    paths = []
    for name in ['lib', 'common', 'x86_64', 'x86', 'backend', 'cfrontend', 'driver', 'cparser']:
        paths += ['-R', f'/compcert/{name}', f'compcert.{name}']
    paths += ['-R', '/compcert/flocq', 'Flocq', '-R', '/compcert/MenhirLib', 'MenhirLib',
              '-R', '/work/export', 'compcert.export', '-Q', '/work/proof', 'QuadratureC']
    files = ['export/Ctypesdefs.v', 'export/Clightdefs.v', 'proof/quadrules.v']
    files += [f'proof/{name}.v' for name in PROOFS + CERTIFICATES]
    files += ['proof/ConfiguredAudit.v']
    logs = []
    for name in files:
        log = work / (Path(name).name + '.log')
        logged(docker([baseline.COQC, '-time'] + paths + [f'/work/{name}']), log)
        logs.append(log.read_text())
    text = '\n'.join(logs)
    (work / 'check.log').write_text(text)
    # Read the dedicated audit: unrelated build diagnostics such as
    # "Warning:" are not declarations in Print Assumptions output.
    audit_log = (work / 'ConfiguredAudit.v.log').read_text()
    assumptions = set()
    for section in audit_log.split('Axioms:\n')[1:]:
        assumptions.update(re.findall(r"^([A-Za-z_][A-Za-z0-9_.']*)[ \t]*:", section, re.M))
    assumptions.discard('Axioms')
    assumptions = {baseline.ASSUMPTION_ALIASES.get(x, x) for x in assumptions}
    if not assumptions or assumptions - baseline.ALLOWED_ASSUMPTIONS:
        raise ValueError(f'Unexpected or missing assumptions: {sorted(assumptions)}')
    audit_count = (audit_log.count('Axioms:\n') +
                   audit_log.count('Closed under the global context'))
    if audit_count != len(AUDITED):
        raise ValueError(f'Expected {len(AUDITED)} audits, got {audit_count}.')
    for name in ['CertifiedPolynomial', 'CertifiedExternal']:
        certificate_log = (work / f'{name}.v.log').read_text()
        if certificate_log.count('Axioms:') != 5:
            raise ValueError(f'{name} must audit all five exported theorems.')
    record = {
        'checked_at': datetime.now(timezone.utc).isoformat(),
        'kind': 'Kernel-checked concrete compilation and integral accuracy in configured CompCert Asm semantics',
        'compcert_base_revision': revision,
        'compcert_is_unmodified_release': False,
        'compcert_target': 'x86_64-linux',
        'coq_version': coq_version,
        'container_image': baseline.IMAGE,
        'container_image_id': capture(['docker', 'image', 'inspect', '--format', '{{.Id}}', baseline.IMAGE]),
        'checker_sha256': checker_sha256,
        'baseline_checker_sha256': baseline_sha256,
        'configuration_patch_sha256': digest(patch),
        'configuration_manifest_sha256': digest(bundle / 'configuration-files.json'),
        'generated_parser_sha256': digest(root / 'cparser/Parser.v'),
        'makefile_config_sha256': digest(root / 'Makefile.config'),
        'configured_source_sha256': {n: digest(root / n) for n in manifest['files']},
        'project_proof_sha256': {f'{n}.v': digest(work / 'proof' / f'{n}.v') for n in PROOFS + CERTIFICATES},
        'clight_source_sha256': baseline.CLIGHT_SHA256,
        'compiler_proof_log_sha256': digest(work / 'compiler-proof.log'),
        'check_log_sha256': digest(work / 'check.log'),
        'logical_and_external_semantics_assumptions': sorted(assumptions),
        'audited_theorems': AUDITED,
        'audit_source_sha256': digest(work / 'proof/ConfiguredAudit.v'),
        'audit_log_sha256': digest(work / 'ConfiguredAudit.v.log'),
        'upstream_computational_parameters': [],
        'all_compcert_proofs_rebuilt_from_source': True,
        'backend_success_kernel_proved': True,
        'compiled_equation_has_no_computational_parameters': True,
        'application_assembly_terminates_proved': True,
        'application_assembly_all_behaviors_proved': True,
        'application_assembly_integral_accuracy_proved': True,
        'successful_compilation_hypothesis': False,
        'result_bits': '3fead02c771c35ed',
        'corrected_absolute_error_bound': '356/100000',
        'draft_absolute_error_bound_refuted': '224/100000',
        'applications': {
            'polynomial_orders_1_to_10': {
                'certificate': 'CertifiedStoredPolynomial.v',
                'origin': 'authored normalized Clight main calling integrate directly; internal degree-14 cosine polynomial',
                'external_cosine_hypotheses': False,
                'successful_compilation_hypothesis': False,
                'result_bits': [
                    '3ff0000000000000', '3fead02c771c35ed',
                    '3feaed9520c8a014', '3feaed5443a06327',
                    '3feaed548f3f6f46', '3feaed548f08f234',
                    '3feaed548f090ce1', '3feaed548f090cce',
                    '3feaed548f090ccf', '3feaed548f090cd4',
                ],
                'absolute_integral_error_bounds': [
                    '159/1000', '356/100000', '31/1000000', '15/100000000',
                    '1/2500000000', '1/1250000000000', '1/500000000000000',
                    '1/250000000000000', '1/250000000000000', '3/1000000000000000',
                ],
            },
            'polynomial_orders_1_to_4': {
                'certificate': 'CertifiedPolynomialRules.v',
                'origin': 'authored normalized Clight main calling integrate directly; internal degree-14 cosine polynomial',
                'external_cosine_hypotheses': False,
                'successful_compilation_hypothesis': False,
                'result_bits': ['3ff0000000000000', '3fead02c771c35ed',
                                '3feaed9520c8a014', '3feaed5443a06327'],
                'absolute_integral_error_bounds': ['159/1000', '356/100000',
                                                 '31/1000000', '15/100000000'],
            },
            'polynomial': {
                'certificate': 'CertifiedPolynomial.v',
                'origin': 'authored normalized Clight entry; replace platform cosine with an internal degree-14 Horner polynomial',
                'external_cosine_hypotheses': False,
                'successful_compilation_hypothesis': False,
            },
            'external': {
                'certificate': 'CertifiedExternal.v',
                'origin': 'authored normalized Clight entry retaining the external cosine declaration',
                'external_cosine_hypotheses': True,
                'successful_compilation_hypothesis': False,
            },
        },
        'compiler_iteration_budget': 10000,
        'allocation_candidate_count': 22,
        'allocation_candidates_validated_in_kernel': True,
        'original_platform_cosine_verified': False,
        'general_lean_to_c_translation_verified': False,
        'assembler_or_linker_verified': False,
        'original_aarch64_apple_binary_verified': False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    print(f'Certificate and full compiler proof checked; evidence: {args.output}', flush=True)


if __name__ == '__main__':
    main()
