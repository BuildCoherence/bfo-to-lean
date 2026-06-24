# Hard-coded — not read from .provenance.json — so a coordinated diff
# that swaps both the vendored bytes and the recorded `repo` field can't
# pass the audit by redirecting it at an attacker mirror.
VENDOR_UPSTREAM_REPO="https://github.com/BFO-ontology/BFO-2020"

VENDOR_EXCLUDED_SUBDIRS=(profiles contributions)
