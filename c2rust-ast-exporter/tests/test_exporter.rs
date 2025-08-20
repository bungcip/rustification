use c2rust_ast_exporter::get_untyped_ast;
use std::fs::File;
use std::io::Write;
use tempdir::TempDir;

#[test]
fn test_static_assert() {
    let tmp_dir = TempDir::new("c2rust_ast_exporter_test").unwrap();
    let file_path = tmp_dir.path().join("test.c");
    let mut file = File::create(&file_path).unwrap();
    file.write_all(b"int main() { _Static_assert(1, \"hello\"); }").unwrap();

    let cc_db_path = tmp_dir.path().join("compile_commands.json");
    let mut cc_db = File::create(&cc_db_path).unwrap();
    let cc_db_content = format!(
        r#"[{{
  "directory": "{}",
  "command": "cc -c {} -o test.o",
  "file": "{}"
}}]"#,
        tmp_dir.path().to_str().unwrap(),
        file_path.to_str().unwrap(),
        file_path.to_str().unwrap()
    );
    cc_db.write_all(cc_db_content.as_bytes()).unwrap();

    let result = get_untyped_ast(&file_path, &cc_db_path, &[], false);
    assert!(result.is_ok());
}
