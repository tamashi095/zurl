#!/usr/bin/env python3
"""Regenerate the differential test vectors in zig-url/testdata/.

wpt_resolve.tsv / wpt_extra_resolve.tsv:
    one test per line, "hex(base)\thex(input)", extracted from the WPT
    urltestdata JSON files (entries with an "input" key; missing/null base
    becomes empty = base-less parse).

The matching *_ada.txt files are produced by running zig-url/dump_ada in
resolve mode (see README.md for the build command):

    zig-url/dump_ada resolve zig-url/testdata/wpt_resolve.tsv \
        > zig-url/testdata/wpt_resolve_ada.txt
    zig-url/dump_ada resolve zig-url/testdata/wpt_extra_resolve.tsv \
        > zig-url/testdata/wpt_extra_ada.txt

The IDNA vectors (idnav2.tsv / toascii.tsv and their .oracle files) are
hex-encoded forms of tests/wpt/IdnaTestV2.json and tests/wpt/toascii.json
with ada::unicode::to_ascii as ground truth; regenerate them the same way
if the WPT files are updated.
"""
import json
import os
import sys

def extract(paths, out):
    n = 0
    with open(out, "w") as f:
        for path in paths:
            with open(path) as fh:
                data = json.load(fh)
            for entry in data:
                if not isinstance(entry, dict) or "input" not in entry:
                    continue
                base = entry.get("base") or ""
                inp = entry["input"]
                if inp is None:
                    inp = ""
                f.write(base.encode("utf-8", "surrogatepass").hex() + "\t" +
                        inp.encode("utf-8", "surrogatepass").hex() + "\n")
                n += 1
    print(out, n)

root = os.path.join(os.path.dirname(__file__), "..", "..")
td = os.path.dirname(__file__)
extract([os.path.join(root, "tests/wpt/urltestdata.json")],
        os.path.join(td, "wpt_resolve.tsv"))
extract([os.path.join(root, "tests/wpt/ada_extra_urltestdata.json")],
        os.path.join(td, "wpt_extra_resolve.tsv"))
