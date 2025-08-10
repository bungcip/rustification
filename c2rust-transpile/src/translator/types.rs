use super::Translation;
use crate::c_ast::CTypeKind;
use crate::c_ast::*;
use crate::diagnostics::TranslationResult;
use syn::*; // To override c_ast::{BinOp,UnOp} from glob import

impl<'c> Translation<'c> {
    pub(crate) fn convert_type(&self, type_id: CTypeId) -> TranslationResult<Box<Type>> {
        if let Some(cur_file) = *self.cur_file.borrow() {
            self.import_type(type_id, cur_file);
        }
        self.type_converter
            .borrow_mut()
            .convert(&self.ast_context, type_id)
    }

    // check if the type is a constant array of pointer (i.e. unsigned char *const[])
    pub(crate) fn check_type_is_constant_aop(&self, type_id: CTypeId) -> Option<CQualTypeId> {
        let type_kind = &self.ast_context.resolve_type(type_id).kind;
        if let CTypeKind::ConstantArray(ctype, _) = type_kind {
            let type_kind = &self.ast_context.resolve_type(*ctype).kind;
            if let CTypeKind::Pointer(cqt) = type_kind {
                return Some(*cqt);
            }
        }
        None
    }

    // display ctype name in nice format for debugging
    // pub(crate) fn debug_ctype_name(&self, ctype: CTypeId) -> String {
    //     let type_kind = &self.ast_context.resolve_type(ctype).kind;
    //     match type_kind {
    //         CTypeKind::Pointer(pointee) => {
    //             let pointee_name = self.debug_ctype_name(pointee.ctype);
    //             let mut qualifiers = String::new();
    //             if pointee.qualifiers.is_const {
    //                 qualifiers.push_str("const ");
    //             }
    //             format!("Pointer({qualifiers}{pointee_name})")
    //         }
    //         CTypeKind::Typedef(decl_id) => {
    //             let decl = self.ast_context.get_decl(decl_id).unwrap();
    //             format!("{:?}", decl)
    //         }
    //         CTypeKind::ConstantArray(ctype, width) => {
    //             format!(
    //                 "ConstantArray({}, {})",
    //                 width,
    //                 self.debug_ctype_name(*ctype)
    //             )
    //         }
    //         CTypeKind::Char => "char".to_string(),
    //         CTypeKind::UChar => "unsigned char".to_string(),
    //         CTypeKind::Short => "short".to_string(),
    //         CTypeKind::UShort => "unsigned short".to_string(),
    //         _ => format!("{:?}", type_kind),
    //     }
    // }
}
