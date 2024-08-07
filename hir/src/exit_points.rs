use crate::passes::exit_points_resolver::ExitPoint;
use std::collections::HashMap;
use transmute_core::ids::ExprId;

#[derive(Debug, PartialEq)]
pub struct ExitPoints {
    pub exit_points: HashMap<ExprId, Vec<ExitPoint>>,
    pub unreachable: Vec<ExprId>,
}
