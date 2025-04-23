use transmute_core::ids::IdentRefId;
use transmute_core::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Annotation {
    pub ident_ref_ids: Vec<IdentRefId>,
    pub span: Span,
}
