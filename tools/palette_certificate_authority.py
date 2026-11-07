"""Frozen authority for the independently qualified complete palette closure.

Only these exact artifacts transport the established conditional proof. A
submitted bundle cannot choose new trust anchors or weaken its conditions.
"""
import base64
import binascii
import json

import palette_native_closure as closure

MAX_BUNDLE_BYTES = 128 * 1024
TRUSTED_PINS = {'original': {'bytes': 1288, 'sha256': 'a82071c2571eda3429a210e1a59d6ce89b0bcd9226e208b5dc2b7c60c9e31542'}, 'linked': {'bytes': 2500, 'sha256': 'fb1dfd42e02758b229f4587e1abb50a1d36274f84088345693fd297b80a40c91'}, 'closure': {'bytes': 11094, 'sha256': '0d056a49edde821a1bfb7799c3cde6e6438695ad963abdec852019684d00480b'}}


def authenticate(artifacts):
    if type(artifacts) is not dict or set(artifacts) != set(TRUSTED_PINS):
        raise ValueError('exact frozen palette artifact set required')
    for name, pin in TRUSTED_PINS.items():
        closure.pinned(artifacts[name], pin, 'independent palette authority ' + name)
    return artifacts


def encode(artifacts):
    authenticate(artifacts)
    raw = json.dumps({name: base64.b64encode(artifacts[name]).decode('ascii')
                      for name in sorted(TRUSTED_PINS)}, sort_keys=True,
                     separators=(',', ':')).encode()
    if len(raw) > MAX_BUNDLE_BYTES:
        raise ValueError('palette artifact bundle exceeds bound')
    return raw


def decode(raw):
    if type(raw) is not bytes or len(raw) > MAX_BUNDLE_BYTES:
        raise ValueError('bounded immutable palette artifact bundle required')
    try:
        values = json.loads(raw, object_pairs_hook=closure.unique,
                            parse_constant=lambda value: (_ for _ in ()).throw(
                                ValueError('nonfinite bundle value')))
        if type(values) is not dict or set(values) != set(TRUSTED_PINS) or any(
                type(value) is not str or not value for value in values.values()):
            raise ValueError('exact base64 palette artifact entries required')
        result = {name: base64.b64decode(value, validate=True)
                  for name, value in values.items()}
        authenticate(result)
        if encode(result) != raw:
            raise ValueError('canonical palette artifact bundle required')
        return result
    except (binascii.Error, UnicodeError, TypeError) as error:
        raise ValueError('malformed palette artifact bundle') from error
