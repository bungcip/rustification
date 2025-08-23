## setup
- need to install LLVM and clang 21
- run `export LLVM_CONFIG_PATH=/usr/bin/llvm-config-21` to set LLVM version to 21
- install python3 requirements.txt 
    `uv venv`
    `uv pip install -r ./scripts/requirements.txt`

## testing
- run `cargo test` for quick testing
- run `uv run scripts/test_translator.py -d tests` for complete testing
- run `uv run scripts/test_translator.py -d tests --only-directories <directory_name>` for just running unit test in `tests/<directory_name>` folder
- create snapshost test in `c2rust-transpile/tests/snapshots`, write a c source file in it to test if changes is working
- don't forget to run `cargo fmt` before creating pull request

