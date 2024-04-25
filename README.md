# VeriSMo: A formally verified security module for AMD confidential VMs.

This repo includes the code for VeriSMo project.

## Files 📁

- tools/ : includes verifier and compiler tools and scripts.
- deps/ : includes hacl package
- source/ : verismo code
- source/verismo : verified code for verismo
- source/verismo_main : main executable bin, which only defines a unverified Rust panic handler.
- source/verismo/src/arch : model
- source/verismo/src/entry.s : a small and unverified assembly code.
- source/target.json : target configuration


## 0. Pre-requirements
First, Install rust toolchain;
```
tools/install.sh
```

## 1. Install tools 🧰
Then, build verus, verus-rustc (replacing rustc) and igvm tools and dependencies.
```
tools/activate.sh
```

## 2. Verify and Build ✔️ 🛠️

Now, run verification checks and build the binary. 

🍵 This step takes several minutes.

### a. Verify the whole project:
Run

```
make verify -f Makefile.default
``` 

or  

```
cd source/verismo_main; cargo build --release;
```

### b. To verify a single module, which is useful for development:
```
cd source/verismo; VERUS_MODULE=security::monitor cargo build --features verifymodule --release;
```

### c. Understand results:

A fully verified result should have "verified": 2138, "errors": 0,


### d. Build without verification 🛠️

If no changes are made in `source/verismo`, we recommend to build without verification to speed up the build process.

```
make verify -f Makefile.default
``` 

or  

```
cd source/verismo_main; cargo build --feature noverify --release;
```

## 3. Create VM image (skip if you run `make` or `make verify`)

1. Run `sh source/target/target/release/verismo/igvm.sh` to generate the verismo in IGVM format for Hyper-V: `source/target/target/release/verismo/verismo-rust.bin`
2. Run `make fs` to generate a vhdx file  as filesystem for the VM: `richos/test-fs/verismo.vhdx`

## 4. Deploy and run

### Requirements

- Hardware: A AMD SEV-SNP machine.
- OS: Windows with a Hypervisor released after 20230909. Earlier release may not support restricted interrupts in both VMPLs and thus will not work.
- Optional: A Debug machine with windows OS.

### Steps

Move following files to your AMD SEV-SNP machine.
- `source/target/target/release/verismo/verismo-rust.bin`
- `richos/test-fs/verismo.vhdx`
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

In source/.cargo/config.toml, we replaced rustc with verus-rustc.
verus-rustc will call `verus` to compile `vstd` (a verus library), `verismo` and `verismo-main` package, and call `rustc` to compile all other packages (hacl, core, etc.).

### Add build.rs to pass additional options to verus tool
See `source/verismo/build.rs`

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
