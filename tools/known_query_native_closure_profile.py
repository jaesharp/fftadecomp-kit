"""Transport the independently qualified known-query effect certificate.

The fixed certificate establishes conditional machine effects only. Current
complete indexed code identities must match every frozen dependency. Native
source capture, fixed compilation, genuine relocations, typed linking and
plausibility remain the existing complete-owner admission path. No old effect
producer is replayed, and no C compatibility or physical permission is added.
"""
import hashlib
import json
from pathlib import Path

from addressed_signed_runtime_profile import toolchain_fingerprint, runtime_fingerprint
from software_double_profile import indices, span_record

SELECTOR = 'conditional-known-query-native-closure-v1'
SCHEMA = 'elf-symbol-thumb-conditional-known-query-native-closure-v1'
CONTROL_FLOW = ('complete initialized two-word query with authenticated known-callback '
                'effects and exact transport; conditional returning ABI, C compatibility '
                'and memory noninterference; termination unproved')
FROZEN_CERTIFICATE = b'{\n  "schema": "conditional-known-query-callback-effects-v1",\n  "address": 134862400,\n  "end": 134862444,\n  "instructions": 18,\n  "body_sha256": "cfa958b3f4cfdee9cd412c162600d7aaf774e78ab6de2ee14e63ee10e3df0c09",\n  "ROM_sha256": "43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19",\n  "mapping_sha256": "2e4c251e4c323e6b19cf9951d06857e7dc6f2ae441a59be5651354fc03f3960f",\n  "index_sha256": "2e636d6032c0471c2008af9761ed609c262fb8d74edda8d5f1f9e990e717f264",\n  "callback_effects": {\n    "schema": "conditional-known-query-callback-effects-v1",\n    "address": 134859240,\n    "end": 134859508,\n    "body_sha256": "871681b6d9767646826ce4fc7e92bdf1a0aa2a8173822cf2a24e3268239c1e19",\n    "instructions": 129,\n    "state_count": 277,\n    "query_reads": [\n      [\n        134859248,\n        0,\n        4\n      ],\n      [\n        134859318,\n        0,\n        4\n      ],\n      [\n        134859352,\n        0,\n        4\n      ]\n    ],\n    "query_writes": [\n      [\n        134859316,\n        4,\n        4,\n        1\n      ],\n      [\n        134859486,\n        4,\n        4,\n        1\n      ]\n    ],\n    "local_reads": [\n      [\n        134859422,\n        -40,\n        4\n      ],\n      [\n        134859424,\n        -20,\n        4\n      ],\n      [\n        134859430,\n        -36,\n        4\n      ],\n      [\n        134859432,\n        -24,\n        4\n      ],\n      [\n        134859438,\n        -48,\n        4\n      ],\n      [\n        134859444,\n        -44,\n        4\n      ],\n      [\n        134859446,\n        -32,\n        4\n      ]\n    ],\n    "local_writes": [\n      [\n        134859360,\n        -40,\n        4\n      ],\n      [\n        134859368,\n        -36,\n        4\n      ],\n      [\n        134859376,\n        -48,\n        4\n      ],\n      [\n        134859384,\n        -44,\n        4\n      ],\n      [\n        134859394,\n        -24,\n        4\n      ],\n      [\n        134859402,\n        -20,\n        4\n      ],\n      [\n        134859410,\n        -32,\n        4\n      ],\n      [\n        134859420,\n        -28,\n        4\n      ]\n    ],\n    "maximum_frame_bytes": 48,\n    "allocated_local_word_offsets": [\n      -48,\n      -44,\n      -40,\n      -36,\n      -32,\n      -28,\n      -24,\n      -20\n    ],\n    "protected_saved_word_offsets": [\n      -16,\n      -12,\n      -8,\n      -4\n    ],\n    "external_accesses": [\n      [\n        134859254,\n        "read",\n        5,\n        0,\n        4\n      ],\n      [\n        134859256,\n        "read",\n        1,\n        24,\n        2\n      ],\n      [\n        134859274,\n        "read",\n        5,\n        0,\n        4\n      ],\n      [\n        134859286,\n        "read",\n        5,\n        0,\n        4\n      ],\n      [\n        134859298,\n        "read",\n        5,\n        28,\n        1\n      ],\n      [\n        134859308,\n        "read",\n        5,\n        29,\n        1\n      ],\n      [\n        134859322,\n        "read",\n        0,\n        10,\n        2\n      ],\n      [\n        134859326,\n        "read",\n        5,\n        10,\n        2\n      ],\n      [\n        134859356,\n        "read",\n        4,\n        8,\n        2\n      ],\n      [\n        134859364,\n        "read",\n        4,\n        8,\n        2\n      ],\n      [\n        134859372,\n        "read",\n        4,\n        12,\n        2\n      ],\n      [\n        134859380,\n        "read",\n        4,\n        12,\n        2\n      ],\n      [\n        134859390,\n        "read",\n        5,\n        8,\n        2\n      ],\n      [\n        134859398,\n        "read",\n        5,\n        8,\n        2\n      ],\n      [\n        134859406,\n        "read",\n        5,\n        12,\n        2\n      ],\n      [\n        134859414,\n        "read",\n        5,\n        12,\n        2\n      ],\n      [\n        134859454,\n        "write",\n        5,\n        28,\n        1\n      ],\n      [\n        134859458,\n        "read",\n        5,\n        28,\n        1\n      ],\n      [\n        134859470,\n        "read",\n        5,\n        14,\n        2\n      ],\n      [\n        134859478,\n        "read",\n        5,\n        16,\n        2\n      ],\n      [\n        134859488,\n        "read",\n        4,\n        31,\n        1\n      ]\n    ],\n    "calls": [\n      [\n        134859264,\n        135060188\n      ],\n      [\n        134859276,\n        135060260\n      ],\n      [\n        134859288,\n        135059756\n      ],\n      [\n        134859340,\n        134858952\n      ],\n      [\n        134859494,\n        134858424\n      ]\n    ],\n    "ordinary_call_observations": [\n      [\n        134859264,\n        135060188,\n        [\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ]\n        ],\n        [\n          "incoming-flag"\n        ]\n      ],\n      [\n        134859276,\n        135060260,\n        [\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ]\n        ],\n        [\n          "incoming-flag"\n        ]\n      ],\n      [\n        134859288,\n        135059756,\n        [\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ]\n        ],\n        [\n          "incoming-flag"\n        ]\n      ],\n      [\n        134859340,\n        134858952,\n        [\n          [\n            "ordinary"\n          ],\n          [\n            "constant",\n            1\n          ],\n          [\n            "constant",\n            10\n          ],\n          [\n            "ordinary"\n          ]\n        ],\n        [\n          "constant",\n          1\n        ]\n      ],\n      [\n        134859340,\n        134858952,\n        [\n          [\n            "ordinary"\n          ],\n          [\n            "constant",\n            1\n          ],\n          [\n            "constant",\n            10\n          ],\n          [\n            "ordinary"\n          ]\n        ],\n        [\n          "incoming-flag"\n        ]\n      ],\n      [\n        134859494,\n        134858424,\n        [\n          [\n            "ordinary"\n          ],\n          [\n            "ordinary"\n          ],\n          [\n            "constant",\n            1\n          ],\n          [\n            "ordinary"\n          ]\n        ],\n        [\n          "constant",\n          1\n        ]\n      ]\n    ],\n    "returns": [\n      [\n        134859506,\n        [\n          "constant",\n          1\n        ]\n      ],\n      [\n        134859506,\n        [\n          "incoming-flag"\n        ]\n      ]\n    ],\n    "returned_private_aliases": [\n      {\n        "site": 134859506,\n        "register": 2,\n        "entry_SP_offset": -32,\n        "lifetime": "expired-at-return"\n      }\n    ],\n    "relation": "query.record unchanged; query.flag is its incoming word or1; returning R0 is1; exact R4-R11/SP/entry-return restored under the listed ordinary-call premises",\n    "tracked_query_or_private_alias_passed_to_ordinary_callees": false,\n    "explicit_conditions": [\n      "Each ordinary call returns to its continuation, preserves R4-R11/SP, and neither reads nor writes the query object, active private/local/saved/incoming frames, or code through any argument, ambient state or hidden alias. No such memory effect is inferred from absence of a tracked argument alias.",\n      "Every external callback access has valid aligned live initialized readable/writable storage as appropriate, and its effective bytes do not overlap the query object, active private frames, saved returns or code.",\n      "The query is an aligned live initialized two-word object. Its designated record read and flag stores are permitted; its record value supplies no private-frame/saved-return provenance.",\n      "Private stack allocation, protected saves and incoming frames are valid, live, nonwrapping and noninterfering; asynchronous mutation, exceptions and faults are not inferred away."\n    ],\n    "ordinary_callee_purity_proved": false,\n    "physical_memory_permission": false,\n    "source_or_ELF_admission": false,\n    "termination_proved": false\n  },\n  "frozen_authorities": {\n    "callback": {\n      "bytes": 2758,\n      "sha256": "48e19801224ad6c31520351ff3a726ba6ce7e4bfa318dcb816a20e2586008e4d"\n    },\n    "transport": {\n      "bytes": 9377,\n      "sha256": "30b99e5e99302f4dc4d450f35c9bcb8f4ac950ce16cf0f44a95238584bed70f3"\n    }\n  },\n  "transport_lift": "Exact wrapper/iterator/adapter/getter/thunk bytes transport the outer query token into callback R1 without dereferencing it. This establishes the known-private-query instance; the old unknown-scalar/no-private-provenance restriction is not silently imported or asserted satisfied.",\n  "frame_layout_relative_to_root_entry_SP": {\n    "query": [\n      -12,\n      -4\n    ],\n    "root_save": [\n      -4,\n      0\n    ],\n    "wrapper_descriptor": [\n      -24,\n      -16\n    ],\n    "wrapper_save": [\n      -16,\n      -12\n    ],\n    "iterator_saves": [\n      -40,\n      -24\n    ],\n    "adapter_saves": [\n      -48,\n      -40\n    ],\n    "callback_local": [\n      -96,\n      -64\n    ],\n    "callback_saves": [\n      -64,\n      -48\n    ]\n  },\n  "query_initialization": {\n    "record": "root entry R1",\n    "flag": 0,\n    "call_argument": "R2 is root entrySP-12"\n  },\n  "query_effect": "For every finite number of completed callbacks, record is unchanged and flag is0or1. A reached flag store sets1; once1 it remains1 under the explicit external-effect conditions.",\n  "stale_alias_transport": {\n    "callback_returns": [\n      {\n        "site": 134859506,\n        "register": 2,\n        "entry_SP_offset": -32,\n        "lifetime": "expired-at-return"\n      }\n    ],\n    "null_record_R2": {\n      "register": 2,\n      "origin": "root-entry-R0",\n      "caller_origin_preserved": true\n    },\n    "no_callback_R2": {\n      "register": 2,\n      "root_entry_SP_offset": -24,\n      "origin": "expired-wrapper-descriptor"\n    },\n    "callback_R2": [\n      {\n        "register": 2,\n        "root_entry_SP_offset": -80,\n        "origin": "expired-callback-local"\n      }\n    ],\n    "nonobservation": "Exact iterator tail and wrapper/root continuations do not read R2. On a later iteration the getter reads onlyR0, then the adapter replaces R2 with the authenticated callback code pointer before the thunk. Expired R2 origins are retained at outer return and are not memory permissions.",\n    "outward_aliases_erased": false,\n    "caller_use_after_outer_return_proved": false\n  },\n  "root_return_origins": {\n    "R0": "zero on null record; query.flag on a returning nonnull path",\n    "R1": "original root entry LR",\n    "R2": "case split retained in stale_alias_transport",\n    "R3_R12": "entry origins on the null/no-callback paths; ordinary callback-clobbered values otherwise"\n  },\n  "return_effect": "Null record returns0 without calling wrapper; a returning nonnull path returns the initialized query flag. Every returning known callback yields1. No iteration count or unconditional return is asserted.",\n  "explicit_conditions": [\n    "Each ordinary call returns to its continuation, preserves R4-R11/SP, and neither reads nor writes the query object, active private/local/saved/incoming frames, or code through any argument, ambient state or hidden alias. No such memory effect is inferred from absence of a tracked argument alias.",\n    "Every external callback access has valid aligned live initialized readable/writable storage as appropriate, and its effective bytes do not overlap the query object, active private frames, saved returns or code.",\n    "The query is an aligned live initialized two-word object. Its designated record read and flag stores are permitted; its record value supplies no private-frame/saved-return provenance.",\n    "Private stack allocation, protected saves and incoming frames are valid, live, nonwrapping and noninterfering; asynchronous mutation, exceptions and faults are not inferred away.",\n    "Every reached owner/list/node/getter load in the authenticated transport is valid, aligned, live and initialized, and does not overlap any active frame, the query or code. No list extent, acyclicity or iterator termination is assumed.",\n    "All nested frames occupy the stated disjoint nonwrapping stack intervals and have valid lifetime/access permissions. The designated query reads and writes are the only permitted observations of the outer query through its transported alias.",\n    "Ordinary callback calls and external accesses preserve the wrapper descriptor, iterator/adapter state, all saved returns and the query record/flag except for the two designated callback flag stores; ambient aliases provide no exemption.",\n    "Concrete C object layout, compatible function types, calling convention and source/ELF binding remain separate admission obligations."\n  ],\n  "old_owner_or_transport_producer_executions": 0,\n  "ordinary_callee_purity_proved": false,\n  "physical_memory_permission": false,\n  "iteration_bound_assumed": false,\n  "termination_proved": false,\n  "source_or_ELF_admission": false,\n  "native_admission": false\n}\n'
CERTIFICATE_SHA256 = 'b10c371942ff73a6ab02c432a45ba9610b6a481ed32eaa9153035935eebbecec'
DEPENDENCIES = ({'address': 134862400, 'end': 134862444, 'instructions': 18, 'body_sha256': 'cfa958b3f4cfdee9cd412c162600d7aaf774e78ab6de2ee14e63ee10e3df0c09'}, {'address': 134846528, 'end': 134846556, 'instructions': 11, 'body_sha256': '55d837fe60c03fad5a01852612f6feabe87d595695bbe421cb506e952ba7c386'}, {'address': 134859240, 'end': 134859508, 'instructions': 129, 'body_sha256': '871681b6d9767646826ce4fc7e92bdf1a0aa2a8173822cf2a24e3268239c1e19'}, {'address': 135036096, 'end': 135036130, 'instructions': 16, 'body_sha256': '47422d610f242091222c8c8e303ea235eede92f9a9c9cc40cd8552e8f44f45d1'}, {'address': 134851560, 'end': 134851582, 'instructions': 9, 'body_sha256': '65ec4ecbbacee97448810c0c4bb966405fc392884ba09795dc94b0b00aeff3d4'}, {'address': 135035764, 'end': 135035768, 'instructions': 2, 'body_sha256': 'a89b85f8bccd76763270edbe8d4a9000e557118189ef0a663b750b93593d16da'}, {'address': 135537244, 'end': 135537246, 'instructions': 1, 'body_sha256': '8726ef5c42206476b80835e7e75d7377ac67a1d964a577f875d20c9dcc98dd97'}, {'address': 135537228, 'end': 135537230, 'instructions': 1, 'body_sha256': 'dd9261f0471768edc33bf979649f6297463be423da17c3f881684f5747e163a1'})
THUNKS = ({'address': 135537244, 'padding_end': 135537248, 'complete_sha256': 'a69cde590b057639cb563cde0b036a97c071c364d199decf423fa3151d2c5ff9'}, {'address': 135537228, 'padding_end': 135537232, 'complete_sha256': 'b6e741ccff336746fdcf62bc30c37deaa54afc60e5be6f8d1c33cfd2b8184ebc'})


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate query certificate member')
        result[key] = value
    return result


def certificate():
    require(type(FROZEN_CERTIFICATE) is bytes and sha(FROZEN_CERTIFICATE) == CERTIFICATE_SHA256,
            'independent query certificate authority differs')
    return json.loads(FROZEN_CERTIFICATE, object_pairs_hook=unique)


def environment_fingerprint():
    return dict(toolchain=toolchain_fingerprint(), runtime=runtime_fingerprint(),
                sources={path.name: sha(path.read_bytes())
                         for path in sorted(Path(__file__).parent.glob('*.py'))})


def prove(data, address, rom, mapping, index, *, selector):
    require(selector == SELECTOR and type(address) is int and
            all(type(raw) is bytes for raw in (data, rom, mapping, index)),
            'explicit known-query native closure and immutable inputs required')
    frozen = certificate()
    require(address == frozen['address'] and len(data) == frozen['end']-address and
            sha(data) == frozen['body_sha256'] and sha(rom) == frozen['ROM_sha256'],
            'complete known-query root or approved full ROM differs')
    entries, rows = indices(mapping, index)
    identities = []
    for expected in DEPENDENCIES:
        lo, hi = expected['address'], expected['end']
        row = span_record(lo, hi, entries, rows, rom)
        body = rom[lo-0x08000000:hi-0x08000000]
        require(row['mode'] == 'thumb' and row['instrs'] == expected['instructions'] and
                sha(body) == expected['body_sha256'],
                'current exact query dependency identity or instruction count differs')
        identities.append(dict(expected))
    require(data == rom[address-0x08000000:frozen['end']-0x08000000],
            'query root bytes differ from current ROM')
    for thunk in THUNKS:
        lo, hi = thunk['address'], thunk['padding_end']
        require(sha(rom[lo-0x08000000:hi-0x08000000]) == thunk['complete_sha256'] and
                not any(int(row['rom'],16) < hi and int(row['end'],16) > lo+2
                        for row in entries), 'separately indexed query thunk padding differs')
    # These pure graph checks partition the current complete root. They do not
    # re-execute the frozen callback interpreter or its earlier owner proofs.
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    refinement = owner.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    partition = graph.partition(data, address, refinement, ins, words)
    require(not branches and not words and len(ins) == frozen['instructions'] and
            sorted(calls) == [address+22], 'query current complete CFG differs')
    return dict(schema=SCHEMA, instructions=len(ins),
        calls=[[site-address, f'func_{target:08X}'] for site,target in sorted(calls.items())],
        runtime_calls=[], partition=partition,
        frozen_conditional_query_effects=frozen,
        certificate_sha256=CERTIFICATE_SHA256, current_dependency_identities=identities,
        mapping_sha256=sha(mapping), index_sha256=sha(index),
        source_sha256={path.name: sha(path.read_bytes()) for path in
                      sorted(Path(__file__).parent.glob('*.py'))},
        explicit_conditions=list(frozen['explicit_conditions']),
        old_effect_or_owner_producer_executions=0,
        conditional_machine_effect_transport=True,
        source_or_ELF_admission=False, native_admission=False,
        physical_memory_permission=False, actual_C_function_compatibility_proved=False,
        termination_proved=False)
