use crate::anonymous_decls::rust_k;

#[test]
pub fn test_anonymous_decl() {
    unsafe {
        assert_eq!((*&raw const rust_k).j.l, 0);
    }
}
