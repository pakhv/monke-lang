use std::{cell::RefCell, collections::HashMap, hash::Hash, ops::Deref, rc::Rc};

use super::types::Object;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Environment {
    pub store: HashMap<String, Object>,
    pub outer: Option<OuterEnvWrapper>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OuterEnvWrapper(pub Rc<RefCell<Environment>>);

impl Deref for OuterEnvWrapper {
    type Target = Rc<RefCell<Environment>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Hash for OuterEnvWrapper {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.borrow().hash(state)
    }
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
            outer: Some(OuterEnvWrapper(outer)),
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

impl Hash for Environment {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let mut to_vec: Vec<_> = self
            .store
            .iter()
            .map(|(key, value)| (key.to_string(), value.to_string()))
            .collect();
        to_vec.sort_by(|(a, _), (b, _)| a.cmp(b));

        to_vec.hash(state);
        self.outer.hash(state);
    }
}
