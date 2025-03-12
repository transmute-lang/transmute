use transmute_core::ids::IdentRefId;
use transmute_core::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Annotation {
    pub ident_ref_id: IdentRefId,
    pub span: Span,
}
