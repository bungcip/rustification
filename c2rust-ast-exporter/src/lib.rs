use serde_cbor::{Value, from_slice};
use std::collections::HashMap;
use std::ffi::{CStr, CString, c_char, c_int};
use std::io::{Error, ErrorKind};
use std::path::Path;
use std::slice;

pub mod clang_ast;

pub fn get_untyped_ast(
    file_path: &Path,
    cc_db: &Path,
    extra_args: &[&str],
    debug: bool,
) -> Result<clang_ast::AstContext, Error> {
    let cbors = get_ast_cbors(file_path, cc_db, extra_args, debug);
    let buffer = cbors
        .values()
        .next()
        .ok_or_else(|| Error::new(ErrorKind::InvalidData, "Could not parse input file"))?;

    // let cbor_path = file_path.with_extension("cbor");
    // let mut cbor_file = File::create(&cbor_path)?;
    // cbor_file.write_all(&buffer[..])?;
    // eprintln!("Dumped CBOR to {}", cbor_path.to_string_lossy());

    let items: Value = from_slice(&buffer[..]).unwrap();

    clang_ast::process(items).map_err(|e| Error::new(ErrorKind::InvalidData, format!("{e}")))
}

fn get_ast_cbors(
    file_path: &Path,
    cc_db: &Path,
    extra_args: &[&str],
    debug: bool,
) -> HashMap<String, Vec<u8>> {
    let mut res = 0;

    let mut args_owned = vec![CString::new("ast_exporter").unwrap()];
    args_owned.push(CString::new(file_path.to_str().unwrap()).unwrap());
    args_owned.push(CString::new("-p").unwrap());
    args_owned.push(CString::new(cc_db.to_str().unwrap()).unwrap());

    for &arg in extra_args {
        args_owned.push(CString::new(["-extra-arg=", arg].join("")).unwrap())
    }

    let args_ptrs: Vec<*const c_char> = args_owned.iter().map(|x| x.as_ptr()).collect();

    let hashmap;
    unsafe {
        let ptr = ast_exporter(
            args_ptrs.len() as c_int,
            args_ptrs.as_ptr(),
            debug.into(),
            &mut res,
        );
        let reference = &*ptr; // SAFETY: ptr is valid until drop_export_result is called
        hashmap = marshal_result(reference);
        drop_export_result(ptr);
    }
    hashmap
}

#[allow(non_camel_case_types)]
#[allow(non_snake_case)]
#[allow(dead_code)]
#[allow(unsafe_op_in_unsafe_fn)]
mod ffi {
    include!(concat!(env!("OUT_DIR"), "/cppbindings.rs"));
}

unsafe extern "C" {
    // ExportResult *ast_exporter(int argc, char *argv[]);
    fn ast_exporter(
        argc: c_int,
        argv: *const *const c_char,
        debug: c_int,
        res: *mut c_int,
    ) -> *mut ffi::ExportResult;

    // void drop_export_result(ExportResult *result);
    fn drop_export_result(ptr: *mut ffi::ExportResult);
}

fn marshal_result(result: &ffi::ExportResult) -> HashMap<String, Vec<u8>> {
    let mut output = HashMap::new();

    let n = result.entries as isize;
    for i in 0..n {
        // Convert name field
        let (cname, csize, cbytes) = unsafe {
            (
                CStr::from_ptr(*result.names.offset(i)),
                *result.sizes.offset(i),
                *result.bytes.offset(i),
            )
        };

        let name = cname.to_str().unwrap().to_owned();

        // Convert CBOR bytes
        let bytes = unsafe { slice::from_raw_parts(cbytes, csize) };
        let mut v = Vec::new();
        v.extend_from_slice(bytes);

        output.insert(name, v);
    }
    output
}
