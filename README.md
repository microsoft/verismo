# VeriSMo: A formally verified security module for AMD confidential VMs.

This repo includes the code for VeriSMo project.

# 📰 News

* **mid-2026 — Copilot-assisted refresh**: verismo now builds and verifies against the latest Verus toolchain.
  * **~10× faster verification**: CI finishes the full proof in ~3 minutes (previously ~30 minutes).
  * **Soundness cleanup**: dropped `assume()` workarounds and unsound proofs that had been added to work around bugs in older Verus.

# 🗞️ READ before using the code

* The code here is a research prototype originally built between 2022-2024; The build and verification still work in this project. However it may not work with current HyperV due to ABI mismatch. The steps to run it in a VM is not tested in recent release; 
* We recommend using this repository as a reference to explore what is possible for low-level verified code (rust-based kernel). For production or ongoing development, please refer to the [Verus project](https://github.com/verus-lang/verus)
 for the latest features and tooling.
* The current implementation does not fully separate executable code from specification/proof code. We are actively exploring incremental verification of real-world systems. For example, [COCONUT-SVSM](https://github.com/coconut-svsm/svsm) is the first open-source project that successfully integrated Verus-based verification into an existing codebase without a full rewrite. You could expect it as a more developer-friendly Rust code with a better verification performance in the future.

## Files 📁

- tools/ : includes verifier and compiler tools and scripts.
- deps/ : includes hacl package
- legacy/source/ : verismo code
- legacy/source/verismo : verified code for verismo
- legacy/source/verismo_main : main executable bin, which only defines a unverified Rust panic handler.
- legacy/source/verismo/src/arch : model
- legacy/source/verismo/src/entry.s : a small and unverified assembly code.
- legacy/source/target.json : target configuration


## 0. Pre-requirements
First, Install rust toolchain;
```
tools/install.sh
```

## 1. Install Verus 🧰
Install the Verus toolchain (verus, rust_verify, z3, cargo-verus, verusfmt) into `~/.cargo/bin`.
By default this downloads the pinned prebuilt release:
```
tools/install_verus
```
Pass `--verus-dir PATH` (optionally with `--verus-rev REV`) to build Verus from a source checkout instead, or `--force` to reinstall when the expected version is already present. Run `tools/install_verus --help` for full usage.

## 2. Install build tools 🧰
Then, build verus-rustc (replacing rustc) and igvm tools and dependencies.
```
tools/activate.sh
```

## 3. Verify and Build ✔️ 🛠️

Now, run verification checks and build the binary. 

🍵 This step takes several minutes.

### a. Verify the whole project:
Run

```
cd legacy/source; cargo verus focus --release;
```

### b. To verify a single module, which is useful for development:

```
cd legacy/source; cargo verus focus -p verismo --release -- --verify-module security::monitor
```

(Pass `-p verismo` or `-p verismo_tspec` to select the package; `--verify-only-module` also works for a single module without dependents.)

### c. Understand results:

A fully verified result should have 

```
verification results:: 852 verified, 0 errors
verification results:: 1281 verified, 0 errors
```


### d. Build without verification 🛠️

If no changes are made in `legacy/source/verismo`, we recommend to build without verification to speed up the build process.

```
make debugbuild
``` 

or  

```
cd legacy/source/verismo_main; cargo verus build -- --no-verify;
```

## 4. Create VM image (skip if you run `make` or `make verify`)

1. Download linux submodule: `git submodule update --init legacy/richos/snplinux`
2. Build guest OS and drivers: `make fs -f Makefile.default`
1. Run `sh legacy/source/target/target/release/verismo/igvm.sh` to generate the verismo in IGVM format for Hyper-V: `legacy/source/target/target/release/verismo/verismo-rust.bin`
2. Run `make fs` to generate a vhdx file  as filesystem for the VM: `legacy/richos/test-fs/verismo.vhdx`

## 5. Deploy and run

### Requirements

- Hardware: A AMD SEV-SNP machine.
- OS: Windows with a Hypervisor released after 20230909. Earlier release may not support restricted interrupts in both VMPLs and thus will not work.
- Optional: A Debug machine with windows OS.

### Steps

Move following files to your AMD SEV-SNP machine.
- `legacy/source/target/target/release/verismo/verismo-rust.bin`
- `legacy/richos/test-fs/verismo.vhdx`
- `tools/vm/*`

#### 1. Create a SNP VM from powershell with admin permission.
```
build-vm.ps1 verismo verismo-rust.bin None verismo.vhdx
```

#### 2. Start the VM

```
start-vm verismo
```

#### 3. Connect to the guest.

GUI-access is not supported and you need to use ssh to login into the guest OS.

The verismo.vhdx includes init process that will open sshd service without password.

Wait for a minute before connecting.
```
ssh root@192.168.0.103
```

#### 4. Talk to VeriSMo module

Once the guest is booted, it has already talked to VeriSMo to wake up AP and update page permissions during its booting.

Inside the guest, we also provided a verismo driver and some tests, to talk to VeriSMo directly if you want.

- verismo.ko: driver
- decode_report: display the binary report to a readable format.
- test.sh: a testing script

```
cd verismo
insmod verismo.ko
sh test.sh
```

#### 5. Optional: You can access the boot log from VeriSMo via a remote debugger.

Refer to windows remote debug to enable both host and hypervisor debugging.
VeriSMo boot log is not accessible from guest OS.


## How build process works 🪄

### Replace rustc with verus-rustc

In legacy/source/.cargo/config.toml, we replaced rustc with verus-rustc.
verus-rustc will call `verus` to compile `vstd` (a verus library), `verismo` and `verismo-main` package, and call `rustc` to compile all other packages (hacl, core, etc.).

### Add build.rs to pass additional options to verus tool
See `legacy/source/verismo/build.rs`

### Features
- noverify: build source without verification
- verifymodule: if ${VERUS_MODULE} is not empty, only verify the specified module.

### Debug vs Release
Depends on cfg(debug_assertations)
Debug mode prints additional messages for debug purpose via leak_debug;
Release mode erase all leak_debug or debug informations;


## Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.opensource.microsoft.com.

When you submit a pull request, a CLA bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

## Trademarks

This project may contain trademarks or logos for projects, products, or services. Authorized use of Microsoft 
trademarks or logos is subject to and must follow 
[Microsoft's Trademark & Brand Guidelines](https://www.microsoft.com/en-us/legal/intellectualproperty/trademarks/usage/general).
Use of Microsoft trademarks or logos in modified versions of this project must not cause confusion or imply Microsoft sponsorship.
Any use of third-party trademarks or logos are subject to those third-party's policies.
