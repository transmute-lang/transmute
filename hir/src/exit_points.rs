use crate::passes::exit_points_resolver::ExitPoint;
use std::collections::HashMap;
use transmute_core::ids::ExprId;

#[derive(Debug, PartialEq)]
pub struct ExitPoints {
    pub exit_points: HashMap<ExprId, Vec<ExitPoint>>,
    // todo:feature do something with it to actually shake the tree and remove the unreachable
    //   nodes
    pub unreachable: Vec<ExprId>,
}
