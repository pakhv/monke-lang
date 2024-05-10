use crate::parser::ast::Program;
use crate::types::Object;
use std::{cell::RefCell, rc::Rc};

pub type AstTraverseNodeRef = Rc<RefCell<AstTraverseNode>>;

#[derive(Debug)]
pub enum AstTraverse {
    Node(AstTraverseNodeRef),
    #[allow(dead_code)]
    None,
}

#[derive(Debug)]
pub struct AstTraverseNode {
    pub parent_node: Option<AstTraverse>,
    pub node: Program,
    pub evaluated_children: Vec<Object>,
}

impl AstTraverse {
    pub fn new(node: Program, parent_node: Option<AstTraverse>) -> Self {
        AstTraverse::Node(Rc::new(RefCell::new(AstTraverseNode {
            evaluated_children: vec![],
            node,
            parent_node,
        })))
    }

    pub fn as_node(&self) -> Option<&AstTraverseNodeRef> {
        match self {
            AstTraverse::Node(node) => Some(node),
            AstTraverse::None => None,
        }
    }
}
