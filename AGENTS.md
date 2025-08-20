## setup
- need to install LLVM and clang 21
- run `export LLVM_CONFIG_PATH=/usr/bin/llvm-config-21` to set LLVM version to 21

## testing
- run `cargo test` for quick testing
- run `python3 ./scripts/test_translator.py -d tests/` for complete testing
- don't forget to run `cargo fmt` before commiting changes
