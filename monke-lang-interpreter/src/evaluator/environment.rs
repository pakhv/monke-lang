use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::types::Object;

#[derive(Debug, Clone)]
pub struct Environment {
    pub store: HashMap<String, Object>,
    pub outer: Option<Rc<RefCell<Environment>>>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment {
            store: HashMap::new(),
            outer: None,
        }
    }

    pub fn new_outer(outer: Rc<RefCell<Environment>>) -> Environment {
        Environment {
            store: HashMap::new(),
            outer: Some(outer),
        }
    }

    pub fn get(&self, name: &String) -> Option<Object> {
        match self.store.get(name) {
            Some(value) => Some(value).cloned(),
            None => match &self.outer {
                Some(value) => value.borrow().get(name),
                None => None,
            },
        }
    }

    pub fn set(&mut self, name: String, val: Object) -> Object {
        self.store.insert(name, val.clone());
        val
    }
}
