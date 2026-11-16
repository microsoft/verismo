# Paging integrations

`litebox/` is the LiteBox Git submodule. The existing local clone was registered
at upstream commit `b6909699288a02c6fdd7c4875b6db7585c11ceac`; its remote is
`https://github.com/microsoft/litebox.git`. No GitHub fork was created.

The LiteBox integration target is **`litebox_platform_lvbs` only**. The Linux-kernel
platform and SNP runner are not integration targets.

`svsm/` is the independent SVSM Git submodule. The existing local clone was
registered at upstream commit `c92252979088d2675ffa27450935e341d3021155`,
using `https://github.com/coconut-svsm/svsm.git` as the submodule URL.
SVSM has a separate opt-in paging backend; its integration and platform
limitations are documented in
[VERISMO_PAGING.md](svsm/Documentation/docs/developer/VERISMO_PAGING.md).

`litebox-old/` retains the earlier Linux-kernel adapter and its
`litebox.patch`. That patch targets an older LiteBox revision and must not be
applied wholesale to this checkout.

Initialize the registered checkout from the Verismo repository root:

```sh
git submodule update --init source/paging/compat/litebox source/paging/compat/svsm
```

Integration implementation notes belong in the LVBS platform's
[README](litebox/litebox_platform_lvbs/README.md).

Changes inside a submodule must be committed in that repository before a
superproject gitlink can record them. Registering this checkout does not commit
or publish its local integration edits.
