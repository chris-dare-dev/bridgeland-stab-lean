#!/usr/bin/env python3
"""Turn `scripts/Audit.lean` into a gate.

`Audit.lean` is a build target, so it cannot rot — but it is **not a gate**:
`#print axioms` prints `[sorryAx]` and exits 0, so a sorry-backed declaration
builds green. This script is what makes the audit fail.

Usage:

    lake env lean scripts/Audit.lean > audit.txt 2>&1
    python3 scripts/check_audit.py audit.txt

Exits non-zero, with the offending declarations named, on any of:

* an axiom outside [propext, Classical.choice, Quot.sound],
* `sorryAx` anywhere,
* an empty sweep (the vacuous pass),
* a **parse mismatch** — see below.

## The parse-mismatch check is not paranoia

An earlier ad-hoc version of this check used `'([^']+)'` to capture the
declaration name. That silently dropped every declaration whose name ends in an
apostrophe — `NormalizedShift.ext'` and `GLTilde.ext'` — because the closing
quote of the printed name is immediately preceded by one. The check reported
187 declarations while the file actually printed 189, and nobody noticed,
because a gate that skips a declaration looks exactly like a gate that passes
it.

So this script counts the marker phrase independently of the structured parse
and fails if the two disagree. A gate that cannot say how much it covered is
not a gate.
"""

from __future__ import annotations

import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

# Lazy, so a name ending in `'` still terminates correctly: the regex needs the
# literal `' depends on axioms: [` to follow, and no declaration name contains
# that.
ENTRY = re.compile(r"'(.+?)' depends on axioms: \[([^\]]*)\]")
NO_AXIOMS = re.compile(r"'(.+?)' does not depend on any axioms")


def main(path: str) -> int:
    raw = open(path, encoding="utf-8").read()
    # `#print axioms` output wraps at the terminal width, unpredictably, so
    # flatten before parsing rather than reading it line by line.
    flat = " ".join(raw.split())

    entries = [(n, {a.strip() for a in axs.split(",") if a.strip()})
               for n, axs in ENTRY.findall(flat)]
    entries += [(n, set()) for n in NO_AXIOMS.findall(flat)]

    # Both report shapes must be counted. `#print axioms` emits "does not depend
    # on any axioms" for an axiom-free declaration, and that phrase does NOT
    # contain "depends on axioms" -- so counting only the first phrase would make
    # `entries` exceed `expected` the moment one such declaration appears, and
    # this guard would fail a run that is in fact fully parsed. Latent today
    # (all 497 currently report axioms), wrong the first time one does not.
    expected = (flat.count("depends on axioms")
                + flat.count("does not depend on any axioms"))
    if len(entries) != expected:
        print(f"::error::audit parse mismatch: parsed {len(entries)} entries but the "
              f"output contains {expected} axiom reports. The gate would be checking "
              f"less than it claims; fix the parser, do not lower the count.")
        return 1

    if not entries:
        print("::error::audit swept 0 declarations -- the vacuous pass")
        return 1

    bad = [(n, sorted(axs - ALLOWED)) for n, axs in entries if not axs <= ALLOWED]
    if bad:
        for name, extra in bad:
            print(f"::error::{name} depends on {extra}")
        print(f"::error::{len(bad)} of {len(entries)} declarations are outside the allowlist")
        return 1

    print(f"ok: {len(entries)} declarations, all within "
          f"[propext, Classical.choice, Quot.sound], no sorryAx")
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
