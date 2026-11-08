"""Index-span bytes row and per-region bars in the status block."""

import re
import sys
from pathlib import Path
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import status


def entry(rom, end):
    return {"rom": f"0x{rom:08X}", "end": f"0x{end:08X}"}


# the badge step of the decomp's status workflow (.github/workflows/status.yml)
def badge_percentages(block):
    pct = {}
    for name in ("functions", "bytes"):
        m = re.search(rf"\| {name.capitalize()} matched \|[^|]*\|\s*\*\*([\d.]+)%\*\*", block)
        if m:
            pct[name] = float(m.group(1))
    return pct


class MergeSpans(unittest.TestCase):
    def test_overlapping_and_touching_spans_merge(self):
        spans = [(0x30, 0x40), (0x00, 0x10), (0x08, 0x18), (0x18, 0x20), (0x34, 0x38)]
        self.assertEqual(status.merge_spans(spans), [[0x00, 0x20], [0x30, 0x40]])

    def test_union_counts_overlap_once(self):
        fns = [entry(0x08000000, 0x08000100), entry(0x08000080, 0x08000180),
               entry(0x08000400, 0x08000410)]
        progress = status.index_progress(fns, [0x08000080])
        self.assertEqual(progress["total"], 0x180 + 0x10)
        self.assertEqual(progress["matched"], 0x100)


class Regions(unittest.TestCase):
    def test_span_crossing_a_region_is_clipped_to_each(self):
        fns = [entry(0x0800FF00, 0x08010100), entry(0x08010200, 0x08010300)]
        progress = status.index_progress(fns, [0x0800FF00])
        regions = {base: rest for base, *rest in progress["regions"]}
        self.assertEqual(len(progress["regions"]), 0x15)
        self.assertEqual(progress["regions"][-1][0], 0x08140000)
        # bytes total, bytes matched, entries, matched entries starting here
        self.assertEqual(regions[0x08000000], [0x100, 0x100, 1, 1])
        self.assertEqual(regions[0x08010000], [0x200, 0x100, 1, 0])
        self.assertEqual(regions[0x08020000], [0, 0, 0, 0])

    def test_entries_at_or_above_code_end_are_only_counted(self):
        fns = [entry(0x0814FFF0, 0x08150000), entry(0x08150000, 0x08150010),
               entry(0x08200000, 0x08200020)]
        progress = status.index_progress(fns, [0x08150000])
        self.assertEqual(progress["late_entries"], 2)
        self.assertEqual(progress["total"], 0x10)
        self.assertEqual(progress["matched"], 0)
        block = status.render(1, 0, 16, 0, [], progress=progress)[0]
        self.assertIn("0x08150000+ assets and data; 2 index entries", block)


class Render(unittest.TestCase):
    fns = [entry(0x08000000, 0x08000100), entry(0x08000080, 0x08000180),
           entry(0x08060000, 0x08060040), entry(0x08200000, 0x08200004)]

    def render(self, progress):
        return status.render(3, 1, 1000, 0x100, [], badge_base="https://x/badges",
                             progress=progress)[0]

    def test_without_progress_the_block_is_unchanged(self):
        block = self.render(None)
        self.assertNotIn("(index span)", block)
        self.assertNotIn("```", block)

    def test_rows_and_regions(self):
        progress = status.index_progress(self.fns, [0x08000000])
        block = self.render(progress)
        self.assertIn("| Bytes matched (index span) | 256 / 448 | **57.14%** | "
                      f"`{status.bar(256 / 448)}` |", block)
        self.assertIn("Both byte denominators are provisional.", block)
        fence = block.split("```")[1].strip("\n").splitlines()
        self.assertEqual(len(fence), 0x15 + 1)
        self.assertEqual(fence[0], f"0x08000000  {status.bar(256 / 384, 20)}   66.7%        1/2 fns")
        self.assertEqual(fence[6], f"0x08060000  {status.bar(0, 20)}    0.0%        0/1 fns")
        self.assertEqual(fence[1], f"0x08010000  {'░' * 20}    0.0%        0/0 fns")
        self.assertEqual(len({len(row) for row in fence[:-1]}), 1)

    def test_badge_regex_reads_the_legacy_rows(self):
        progress = status.index_progress(self.fns, [0x08000000])
        block = self.render(progress)
        self.assertEqual(badge_percentages(block), {"functions": 33.33, "bytes": 25.6})
        self.assertEqual(badge_percentages(self.render(None)), badge_percentages(block))


if __name__ == "__main__":
    unittest.main()
