# Agent Instructions for c2rust

This document provides instructions for AI agents working on the `c2rust` codebase.

## Project Overview

This is a fork of the original `c2rust` project, focusing solely on the C-to-Rust transpiler. The goal is to translate C99 compliant code into unsafe Rust. The project is a Rust workspace composed of several crates.

For more general information about the project, please see `README.md`. For the most up-to-date build and test information, refer to the CI workflow at `.github/workflows/ci.yml`.

## Environment Setup

To work on this project, you will need to set up your environment as follows:

1.  **Install LLVM and Clang:**
    This project requires LLVM and Clang version 21. You can install it using your system's package manager. For a reliable setup method, refer to the `LLVM Install` step in the CI workflow at `.github/workflows/ci.yml`.

2.  **Set LLVM Environment Variable:**
    After installing LLVM, you must set the `LLVM_CONFIG_PATH` environment variable to point to the `llvm-config-21` executable.
    ```bash
    export LLVM_CONFIG_PATH=/usr/bin/llvm-config-21
    ```

3.  **Install Python Dependencies:**
    The project uses Python scripts for testing. You will need `uv` to install the dependencies.
    ```bash
    uv venv
    uv pip install -r ./scripts/requirements.txt
    ```

4.  **Install Other Dependencies:**
    The project also requires `cmake`. You can install it using your system's package manager.

## Building the Project

To build the project, run the following command:

```bash
cargo build --release
```

## Testing

There are several ways to test the project. It is recommended to run all tests before submitting your changes.

1.  **Check Code Formatting:**
    Ensure your code is correctly formatted by running:
    ```bash
    cargo fmt --check
    ```
    To automatically fix formatting issues, run `cargo fmt`.

2.  **Run Rust Tests:**
    Run the Rust unit and integration tests with:
    ```bash
    cargo test --release
    ```

3.  **Run the Full Transpiler Test Suite:**
    This is the main test suite for the transpiler. It is a Python script that translates and tests a large number of C files.
    ```bash
    uv run scripts/test_translator.py tests
    ```
    You can run tests for a specific directory by using the `--only-directories` flag:
    ```bash
    uv run scripts/test_translator.py tests --only-directories <directory_name>
    ```

4.  **Snapshot Tests:**
    The transpiler uses snapshot tests to verify the generated Rust code. These tests are located in `c2rust-transpile/tests/snapshots`. To add a new snapshot test, create a new C source file in that directory. The test suite will automatically pick it up, generate a `.snap` file, and compare the output on subsequent runs.
