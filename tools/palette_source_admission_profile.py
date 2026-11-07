"""Fresh compiler origin for one independently authenticated conditional palette.

This discharges only source capture/fixed compilation and typed ELF transport.
Every nested false flag and C/ABI/access/frame premise is retained verbatim.
The byte MATCH verdict does not establish unconditional source definedness,
physical permission, termination or native admission.
"""
import argparse
from contextvars import ContextVar
import importlib
import json
from pathlib import Path
import re
import shlex
import struct
import subprocess
import sys
import tempfile

import match
import palette_certificate_authority as authority
import palette_original_transport as transport
from palette_native_closure import require, sha, unique
from inert_spin_profile import fixed_configuration, index_snapshot, marker_text
from addressed_signed_runtime_profile import toolchain_fingerprint, runtime_fingerprint

SELECTOR = 'conditional-palette-source-compilation-v1'
SCHEMA = 'elf-symbol-thumb-conditional-palette-source-compilation-v1'
CONTRACT = ('fresh fixed-compiler source origin and exact typed ELF transport of an '
            'authenticated conditional palette closure; all C layout/conversion, live '
            'object/frame/provenance/noninterference and physical access conditions retained')
_replay = ContextVar('palette_source_compilation_replay', default=False)


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def producer_fingerprint():
    paths = {p.name: p for p in Path(__file__).parent.glob('*.py')}
    for name in ('match', 'match_evidence', __name__):
        p = Path(importlib.import_module(name).__file__)
        paths[p.name] = p
    return {name: sha(p.read_bytes()) for name, p in sorted(paths.items())}


def selector_for_report(report):
    lines = report.splitlines()
    if not any(SCHEMA in line or marker_text(line).startswith('* palette source') for line in lines):
        return None
    require([line for line in lines if marker_text(line).startswith('* verification')] ==
            [f'* verification: `{SCHEMA}`'] and
            [line for line in lines if marker_text(line).startswith('* palette source:')] ==
            [f'* palette source: `{SELECTOR}`'], 'mixed or malformed palette source report')
    return SELECTOR


def selected(report):
    return selector_for_report(report) is not None


def saved_evidence(report):
    require(selected(report), 'explicit palette source report required')
    prefix = '* palette source evidence: `'
    rows = [line for line in report.splitlines() if line.startswith(prefix)]
    require(len(rows) == 1 and rows[0].endswith('`') and len(rows[0]) < 1024*1024,
            'one bounded palette evidence record required')
    encoded = rows[0][len(prefix):-1]
    value = json.loads(encoded, object_pairs_hook=unique)
    require(text(value) == encoded, 'noncanonical palette evidence')
    return value


def configuration(args):
    fixed_configuration(args)
    require(getattr(args, 'owner_runtime_profile', None) == SELECTOR and
            args.mode == 'thumb' and args.control_flow_profile == 'ordinary' and
            not args.label and args.wsl == 'Ubuntu' and args.wsl_path == match.DEFAULT_WSL_PATH and
            not any(value is not None for name, value in vars(args).items()
                    if name.endswith('_profile') and name not in
                    ('owner_runtime_profile', 'control_flow_profile')),
            'palette source requires its isolated explicit Thumb selector')


def default_arguments():
    return argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS,
        owner_runtime_profile=SELECTOR, mode='thumb', control_flow_profile='ordinary',
        label='', wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH, palette_closure_bundle=None)


def bundle_for(root, address, args, expected):
    path = getattr(args, 'palette_closure_bundle', None)
    require(not (path is not None and expected is not None), 'replay cannot replace embedded palette authority')
    if path is not None:
        path = Path(path)
        raw = (path if path.is_absolute() else root/path).read_bytes()
    elif expected is not None:
        raw = expected['artifact_bundle'].encode('ascii')
    else:
        report = (root/'docs/match'/f'{address:08X}.md').read_text()
        raw = saved_evidence(report)['manifest']['artifact_bundle'].encode('ascii')
    authority.decode(raw)
    return raw


def preflight(bundle, address, source, rom, mapping, index, objects, tools):
    artifacts = authority.decode(bundle)
    prior = json.loads(artifacts['closure'], object_pairs_hook=unique)
    require(prior['address'] == address and sha(source) == prior['source_sha256'] and
            sha(rom) == prior['ROM_sha256'] and tools == prior['environment']['toolchain'],
            'frozen source, owner, ROM or fixed toolchain differs')
    entries, rows = transport.spans.indices(mapping, index)
    for start, end, count, digest in (prior['dependency_context']['owner'],
                                      prior['dependency_context']['helper']):
        require(transport.spans.span_record(start, end, entries, rows, rom)['instrs'] == count and
                sha(rom[start-match.ROM_BASE:end-match.ROM_BASE]) == digest,
                'current complete palette dependency or count differs')
    # Also validate all current named data identities before spending a compile.
    binding_plan(artifacts['original'], address, bundle, objects)
    return artifacts, prior


def binding_plan(raw, address, bundle, objects):
    """Only genuine original zero-addend relocations may acquire fixed types."""
    artifacts = authority.decode(bundle)
    prior = json.loads(artifacts['closure'], object_pairs_hook=unique)
    require(address == prior['address'], 'palette binding owner differs')
    size = prior['end']-address
    old = transport.image(artifacts['original'], address, size, 1)
    live = transport.image(raw, address, size, 1)
    linked = transport.image(artifacts['linked'], address, size, 2)
    records = transport.relocations(live, size)
    require(live['text'] == old['text'] and records == transport.relocations(old, size),
            'fresh original text or relocation identity differs from frozen authority')
    bindings = prior['bindings']
    require(not bindings['functions'] and not bindings['switches'] and
            len(bindings['calls']) == 1 and bindings['calls'][0][1] == 'memcpy' and
            len({name for _, name, _ in bindings['data']}) == 2,
            'exact compiler memcpy and two data identities required')
    expected = sorted([(site, 10, name) for site, name in bindings['calls']] +
                      [(site, 2, name) for site, name, addend in bindings['data'] if addend == 0])
    require([(site, kind, name) for site, kind, name, _ in records] == expected,
            'complete frozen relocation roles differ')
    data = match.parse_data_symbols(objects)
    targets = {}
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB); decoder.detail = True
    for site, kind, name, _ in records:
        require(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name) is not None,
                'unsafe assembly identity')
        symbol = transport.closure.unique_symbol(linked, name)
        if kind == 10:
            ins = next(decoder.disasm(live['text'][site:site+4], address+site), None)
            point = prior['dependency_context']['helper'][0] | 1
            require(ins is not None and ins.id == match.ARM_INS_BL and ins.size == 4 and
                    ins.operands[0].imm == address+site and name == 'memcpy',
                    'original memcpy is not a genuine zero-addend Thumb BL')
            expected_type = 2
        else:
            require(struct.unpack_from('<I', live['text'], site)[0] == 0 and name in data and
                    list(data.values()).count(data[name]) == 1,
                    'canonical unique zero-addend data binding required')
            point, expected_type = data[name], 1
        require(symbol['bind'] == 1 and symbol['section'] == 0xfff1 and symbol['size'] == 0 and
                (symbol['value'], symbol['type']) == (point, expected_type),
                'current typed binding differs from authenticated linked identity')
        targets[name] = (point, expected_type)
    return targets


def link_original(runner, workspace, args, raw, address, bundle, objects):
    targets = binding_plan(raw, address, bundle, objects)
    definitions = ['.syntax unified', '.thumb']
    for name, (point, kind) in sorted(targets.items()):
        if kind == 2:
            definitions += [f'.global {name}', f'.type {name}, %function',
                            f'.thumb_set {name}, 0x{point:08X}']
        else:
            definitions += [f'.global {name}', f'.type {name}, %object',
                            f'.set {name}, 0x{point:08X}']
    runner.write_text(workspace+'/f.known.s', '\n'.join(definitions)+'\n')
    runner.write_text(workspace+'/f.ld',
        f'SECTIONS {{ .text 0x{address:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
        '.data 0 : { *(.data) } .bss 0 : { *(.bss) } .ARM.attributes 0 : { *(.ARM.attributes) } '
        '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
        '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
        'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") '
        '/DISCARD/ : { *(.comment) *(.note.GNU-stack) } }')
    quoted = shlex.quote(workspace)
    runner.sh(f'export TMPDIR={quoted}; {args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o')
    runner.sh(f'export TMPDIR={quoted}; {args.linker} --fatal-warnings --no-undefined --no-relax '
              f'--orphan-handling=error -T {quoted}/f.ld -e func_{address:08X} '
              f'{quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf')
    require(runner.read_binary(workspace+'/f.o') == raw, 'original compiler object changed during link')
    return runner.read_binary(workspace+'/f.elf')


def context(root, address):
    from match_evidence import source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    rom_path = report_rom_path(root)
    return dict(source=source_fingerprint(root, address), mapping=mapping_snapshot(root),
        index=index_snapshot(root), objects=data_snapshot(root), rom_path=str(rom_path),
        rom=Path(rom_path).read_bytes(), tools=toolchain_fingerprint(),
        runtime=runtime_fingerprint(), producers=producer_fingerprint())


def build(root, address, args=None, expected=None):
    from match_evidence import source_paths, source_fingerprint
    root, args = Path(root), args or default_arguments()
    configuration(args)
    candidates = list((root/'src').rglob(f'{address:08X}.c'))
    require(len(candidates) == 1, 'one unique palette source required')
    source_path = candidates[0].relative_to(root)
    before = context(root, address)
    bundle = bundle_for(root, address, args, expected)
    preflight(bundle, address, candidates[0].read_bytes(), before['rom'], before['mapping'],
              before['index'], before['objects'], before['tools'])
    (root/'build').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='palette_source_', dir=root/'build') as directory:
        capture = Path(directory)
        for path in source_paths(root, address):
            target = capture/path.relative_to(root)
            target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(path.read_bytes())
        require(source_fingerprint(capture, address) == before['source'], 'palette source capture changed')
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=capture, timeout=120)
        with runner.workspace() as workspace:
            raw, _, _ = match.compile_object(runner, workspace, args, capture, address, source_path.as_posix())
            intermediate = {name: sha(runner.read_binary(workspace+'/f.'+suffix))
                            for name, suffix in (('preprocessed', 'i'), ('assembly', 's'))}
            linked = link_original(runner, workspace, args, raw, address, bundle, before['objects'])
            proof, count = transport.verify_original(raw, linked, address, before['rom'], before['mapping'],
                before['index'], before['objects'], (capture/source_path).read_bytes(), bundle,
                selector=transport.SELECTOR)
        checker = Path(importlib.import_module('plausible').__file__)
        process = match._run_replay_process([sys.executable, str(checker), '--quiet', '--addr',
            f'0x{address:08X}', '--json']+[str(path) for path in source_paths(capture, address)], capture, 120)
        findings, allowed = match.plausibility_result(process, address)
        require(not findings and not allowed and source_fingerprint(capture, address) == before['source'],
                'palette source is implausible, allow-listed or changed')
    require(context(root, address) == before, 'palette source/maps/ROM/tools/runtime/producers changed')
    require(proof['fresh_fixed_compiler_source_replay_required'] is True and all(proof[key] is False
            for key in ('native_admission', 'source_or_ELF_admission', 'physical_memory_permission',
                        'unconditional_termination')), 'transport conditional boundary changed')
    manifest = dict(schema=SCHEMA, selector=SELECTOR, contract=CONTRACT,
        artifact_bundle=bundle.decode('ascii'), transport=proof,
        fresh_fixed_compiler_source_origin=True, conditional_source_compilation=True,
        discharged_obligation='fresh_fixed_compiler_source_replay_required of the retained transport',
        native_admission=False, source_or_ELF_admission=False, physical_memory_permission=False,
        unconditional_termination=False, producer_source_sha256=before['producers'],
        compiler_flags=args.flags, source_path=source_path.as_posix(), intermediate_sha256=intermediate,
        original_elf_sha256=sha(raw), linked_elf_sha256=sha(linked), compiler_executions=1,
        old_complete_closure_executions=0)
    require(expected is None or text(expected) == text(manifest), 'palette source manifest differs')
    body = match.elf_image(linked)['text']
    return dict(address=address, body=body, manifest=manifest, source_sha256=before['source'],
        mapping_sha256=sha(before['mapping']), index_sha256=sha(before['index']),
        objects_sha256=sha(before['objects']), rom_sha256=sha(before['rom']), instructions=count,
        toolchain=before['tools'], runtime=before['runtime'], original_elf=raw, linked_elf=linked)


def render(result):
    evidence = {key: value for key, value in result.items() if key not in ('body', 'original_elf', 'linked_elf')}
    for key in ('body', 'original_elf', 'linked_elf'): evidence[key+'_sha256'] = sha(result[key])
    return '\n'.join([f'# 0x{result["address"]:08X}', '', f'* verification: `{SCHEMA}`',
        f'* palette source: `{SELECTOR}`', f'* control flow: {CONTRACT}',
        '* verified extent: complete original ELF function symbol, including literal pools',
        '* admission scope: conditional source compilation only; nested native/source/physical/termination false flags retained',
        '* relocations: none', '* source plausibility: plausible', '* hand-asm allow list: not listed',
        f'* palette source evidence: `{text(evidence)}`',
        f'* palette source proof SHA-256: `{sha(text(evidence).encode())}`',
        f'* compiled : `{result["body"].hex()}`',
        f'* ROM bytes: `{result["body"].hex()}` ({len(result["body"])} bytes)', '',
        f'**MATCH - byte identical** - {len(result["body"])}/{len(result["body"])} bytes', ''])


def report_matches(report, root, address):
    if _replay.get(): return False
    token = _replay.set(True)
    try:
        saved = saved_evidence(report)
        now = context(Path(root), address)
        require(saved['address'] == address and saved['source_sha256'] == now['source'] and
                all(saved[key+'_sha256'] == sha(now[key]) for key in ('mapping', 'index', 'objects', 'rom')) and
                saved['toolchain'] == now['tools'] and saved['runtime'] == now['runtime'] and
                saved['manifest']['producer_source_sha256'] == now['producers'],
                'saved palette context differs')
        return render(build(root, address, expected=saved['manifest'])) == report
    except (OSError, ValueError, KeyError, TypeError, IndexError, RuntimeError, subprocess.SubprocessError):
        return False
    finally:
        _replay.reset(token)


def issue(root, address, args):
    configuration(args)
    result = build(root, address, args)
    if args.emit:
        output = (Path(root)/args.emit).resolve()
        require((Path(root)/'build').resolve() in output.parents and not output.exists(),
                '--emit requires a new file beneath build/')
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open('xb') as stream: stream.write(result['body'])
    if not args.no_write:
        path = Path(root)/'docs/match'/f'{address:08X}.md'
        path.parent.mkdir(parents=True, exist_ok=True); path.write_text(render(result))
    print(f'extent    {len(result["body"])} bytes (conditional palette source compilation)')
    print('scope     conditional source compilation only; native admission remains false')
    print('verdict MATCH - byte identical')
    return 0
