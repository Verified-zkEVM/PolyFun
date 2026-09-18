# Documentation consumer

This separate Lake package checks that the public tutorial and interaction APIs
work through ordinary imports. Run it from the repository root:

```bash
lake -d test/DocumentationConsumer build --wfail
```

Its toolchain matches the parent checkout, it uses PolyFun's dependency pins, and it shares
its package cache. The package's manifest and build outputs are local artifacts.
The full `./scripts/validate.sh --test` workflow and CI's test job run this check.

Add an assertion here when an example relies on a public equation across a
package boundary. Keep implementation-level regression tests in `PolyFunTest/`.
