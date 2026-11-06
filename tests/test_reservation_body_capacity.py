import copy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import reserve


TIMESTAMP = "2026-11-06T00:00:00Z"


def comment(request_id, operation="claim", address="0x08011040", **fields):
    defaults = {"claim": dict(note="natural source attempt"),
                "ping": {}, "release": dict(reason="stopped", unmatchable=False, tried="")}
    request = dict(operation=operation, address=address, who="lane", **defaults[operation])
    request.update(fields)
    return {"id": request_id, "user": {"id": 7, "type": "User"},
            "body": reserve.REQUEST_PREFIX + json.dumps(request)}


def apply(state, entry):
    return reserve.apply_comment(state, entry, set(), TIMESTAMP,
                                 claim_check=lambda address: (0, "FREE"))


def full_receipts():
    state = apply(dict(version=1, cursor=0, rows=[], results=[]), comment(1))
    for request_id in range(2, 66):
        state = apply(state, comment(request_id))
    return state


class ReservationBodyCapacityTests(unittest.TestCase):
    def test_claim_evicts_old_receipts_without_changing_existing_leases(self):
        state = full_receipts()
        original = copy.deepcopy(state)
        limit = len(reserve.render(state).encode())
        with patch.object(reserve, "MAX_BODY_BYTES", limit):
            result = apply(state, comment(66, address="0x08011080"))
            self.assertLessEqual(len(reserve.render(result).encode()), limit)
            self.assertEqual(reserve.parse_ledger(reserve.render(result)), result)
        self.assertEqual(state, original)
        self.assertEqual(result["rows"][:-1], original["rows"])
        self.assertEqual(result["rows"][-1]["address"], "0x08011080")
        self.assertEqual(result["results"][-1]["status"], "accepted")
        self.assertEqual(result["results"][-1]["request_id"], 66)
        self.assertLess(len(result["results"]), reserve.MAX_RESULTS)

    def test_longer_rejection_can_advance_the_full_ledger(self):
        state = full_receipts()
        limit = len(reserve.render(state).encode())
        # This reaches the longer authenticated-ownership rejection, rather
        # than the shorter duplicate-claim receipt currently filling the body.
        request = comment(66, "release", claim_id=2, reason="stopped")
        with patch.object(reserve, "MAX_BODY_BYTES", limit):
            result = apply(state, request)
            self.assertLessEqual(len(reserve.render(result).encode()), limit)
        self.assertEqual(result["rows"], state["rows"])
        self.assertEqual(result["cursor"], 66)
        self.assertEqual(result["results"][-1]["status"], "rejected")
        self.assertIn("does not match", result["results"][-1]["message"])

    def test_release_at_capacity_preserves_receipts_and_other_leases(self):
        state = full_receipts()
        with patch.object(reserve, "MAX_BODY_BYTES", len(reserve.render(state).encode())):
            result = apply(state, comment(66, "release", claim_id=1, reason="stopped"))
        self.assertEqual(result["rows"], [])
        self.assertEqual(len(result["results"]), reserve.MAX_RESULTS)
        self.assertEqual(result["results"][-1]["status"], "accepted")

    def test_rows_cannot_displace_the_newest_rejection_receipt(self):
        state = apply(dict(version=1, cursor=0, rows=[], results=[]), comment(1))
        original = copy.deepcopy(state)
        limit = len(reserve.render(state).encode()) + 300
        with patch.object(reserve, "MAX_BODY_BYTES", limit):
            result = apply(state, comment(2, address="0x08011080", note="x" * 400))
            self.assertLessEqual(len(reserve.render(result).encode()), limit)
        self.assertEqual(state, original)
        self.assertEqual(result["rows"], state["rows"])
        self.assertEqual(result["results"][-1]["request_id"], 2)
        self.assertEqual(result["results"][-1]["status"], "rejected")

    def test_impossible_rejection_leaves_the_input_state_untouched(self):
        state = dict(version=1, cursor=0, rows=[], results=[])
        original = copy.deepcopy(state)
        with patch.object(reserve, "MAX_BODY_BYTES", len(reserve.render(state).encode())):
            with self.assertRaises(reserve.LedgerError):
                apply(state, comment(1))
        self.assertEqual(state, original)

    def test_invalid_state_is_not_repaired_by_receipt_eviction(self):
        state = full_receipts()
        state["rows"][0]["owner_id"] = 0
        with self.assertRaises(reserve.LedgerError):
            apply(state, comment(66, address="0x08011080"))


if __name__ == "__main__":
    unittest.main()
