use crate::ids::ExprId;
use crate::hir::passes::exit_points_resolver::ExitPoint;
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
pub struct ExitPoints {
    pub exit_points: HashMap<ExprId, Vec<ExitPoint>>,
    pub unreachable: Vec<ExprId>,
}
