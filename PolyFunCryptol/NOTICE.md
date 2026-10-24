# Third-party notices

PolyFunCryptol is part of PolyFun and is licensed under Apache 2.0. Some of its
files are derived from, or describe, the third-party projects below.

## Cryptol

Copyright (c) 2013-2023 Galois Inc. Licensed under the BSD 3-Clause License; the
complete text is [`artifacts/references/cryptol-license.txt`](artifacts/references/cryptol-license.txt).

- `exporter/patches/case-binder-types.patch` modifies Cryptol source at commit
  `61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b`.
- The exported bundles under `artifacts/` contain the typed abstract syntax of
  Cryptol's prelude and `Cryptol::Reference` library at that commit.

## Foundation

Developed at the National Security Agency and licensed under Apache 2.0; see its
[NOTICE](https://github.com/NationalSecurityAgency/Foundation/blob/7d0528bd998682788f4e23661f2829298f9e47db/NOTICE.md).
`artifacts/foundation-status.json` and `artifacts/evaluator-audit.json` record
declaration names, file digests and expressions from Foundation at commit
`7d0528bd998682788f4e23661f2829298f9e47db`. No Foundation source file is
redistributed here.
