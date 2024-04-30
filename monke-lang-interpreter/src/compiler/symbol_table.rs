use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

#[derive(Debug, PartialEq, Clone)]
pub enum SymbolScope {
    Global,
    Local,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Symbol {
    pub name: String,
    pub scope: SymbolScope,
    pub index: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SymbolTable {
    pub store: HashMap<String, Symbol>,
    pub outer: Option<SymbolTableRef>,
    pub definitions_num: usize,
}

pub type SymbolTableRef = Rc<RefCell<SymbolTable>>;

#[derive(Debug, Clone)]
pub struct SymbolTableWrapper(pub SymbolTableRef);

impl Deref for SymbolTableWrapper {
    type Target = SymbolTableRef;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl SymbolTable {
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            store: HashMap::new(),
            outer: None,
            definitions_num: 0,
        }))
    }

    pub fn define(&mut self, name: String) -> Symbol {
        let symbol = Symbol {
            name: name.clone(),
            index: self.definitions_num,
            scope: match self.outer {
                Some(_) => SymbolScope::Local,
                None => SymbolScope::Global,
            },
        };

        self.store.insert(name, symbol.clone());
        self.definitions_num += 1;

        symbol
    }

    pub fn resolve(&self, name: &str) -> Option<Symbol> {
        let result = self.store.get(name);

        match result {
            Some(symbol) => Some(symbol.clone()),
            None => match &self.outer {
                Some(outer) => outer.borrow_mut().resolve(name),
                None => None,
            },
        }
    }

    pub fn new_enclosed(outer: SymbolTableRef) -> SymbolTableRef {
        let new_table = SymbolTable::new();
        new_table.borrow_mut().outer = Some(outer);

        new_table
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn define_test() {
        let expected = HashMap::from([
            (
                String::from("a"),
                Symbol {
                    name: String::from("a"),
                    scope: SymbolScope::Global,
                    index: 0,
                },
            ),
            (
                String::from("b"),
                Symbol {
                    name: String::from("b"),
                    scope: SymbolScope::Global,
                    index: 1,
                },
            ),
        ]);

        let table = SymbolTable::new();
        let a = table.borrow_mut().define(String::from("a"));
        let b = table.borrow_mut().define(String::from("b"));

        assert_eq!(expected["a"], a);
        assert_eq!(expected["b"], b);
    }

    #[test]
    fn resolve_global_test() {
        let table = SymbolTable::new();
        table.borrow_mut().define(String::from("a"));
        table.borrow_mut().define(String::from("b"));

        let expected = HashMap::from([
            (
                String::from("a"),
                Symbol {
                    name: String::from("a"),
                    scope: SymbolScope::Global,
                    index: 0,
                },
            ),
            (
                String::from("b"),
                Symbol {
                    name: String::from("b"),
                    scope: SymbolScope::Global,
                    index: 1,
                },
            ),
        ]);

        for (name, symbol) in expected.iter() {
            let result = table.borrow();
            let result = result.resolve(name);

            assert!(result.is_some());
            assert_eq!(symbol, &result.unwrap());
        }
    }

    #[test]
    fn resolve_local_test() {
        let global = SymbolTable::new();
        global.borrow_mut().define(String::from("a"));
        global.borrow_mut().define(String::from("b"));

        let local = SymbolTable::new_enclosed(global);
        local.borrow_mut().define(String::from("c"));
        local.borrow_mut().define(String::from("d"));

        let expected = HashMap::from([
            (
                String::from("a"),
                Symbol {
                    name: String::from("a"),
                    scope: SymbolScope::Global,
                    index: 0,
                },
            ),
            (
                String::from("b"),
                Symbol {
                    name: String::from("b"),
                    scope: SymbolScope::Global,
                    index: 1,
                },
            ),
            (
                String::from("c"),
                Symbol {
                    name: String::from("c"),
                    scope: SymbolScope::Local,
                    index: 0,
                },
            ),
            (
                String::from("d"),
                Symbol {
                    name: String::from("d"),
                    scope: SymbolScope::Local,
                    index: 1,
                },
            ),
        ]);

        for (name, symbol) in expected.iter() {
            let result = local.borrow();
            let result = result.resolve(name);

            assert!(result.is_some());
            assert_eq!(symbol, &result.unwrap());
        }
    }

    #[test]
    fn resolve_nested_local_test() {
        let global = SymbolTable::new();
        global.borrow_mut().define(String::from("a"));
        global.borrow_mut().define(String::from("b"));

        let first_local = SymbolTable::new_enclosed(global);
        first_local.borrow_mut().define(String::from("c"));
        first_local.borrow_mut().define(String::from("d"));

        let second_local = SymbolTable::new_enclosed(Rc::clone(&first_local));
        second_local.borrow_mut().define(String::from("e"));
        second_local.borrow_mut().define(String::from("f"));

        let expected = [
            (
                Rc::new(&first_local),
                [
                    Symbol {
                        name: String::from("a"),
                        scope: SymbolScope::Global,
                        index: 0,
                    },
                    Symbol {
                        name: String::from("b"),
                        scope: SymbolScope::Global,
                        index: 1,
                    },
                    Symbol {
                        name: String::from("c"),
                        scope: SymbolScope::Local,
                        index: 0,
                    },
                    Symbol {
                        name: String::from("d"),
                        scope: SymbolScope::Local,
                        index: 1,
                    },
                ],
            ),
            (
                Rc::new(&second_local),
                [
                    Symbol {
                        name: String::from("a"),
                        scope: SymbolScope::Global,
                        index: 0,
                    },
                    Symbol {
                        name: String::from("b"),
                        scope: SymbolScope::Global,
                        index: 1,
                    },
                    Symbol {
                        name: String::from("e"),
                        scope: SymbolScope::Local,
                        index: 0,
                    },
                    Symbol {
                        name: String::from("f"),
                        scope: SymbolScope::Local,
                        index: 1,
                    },
                ],
            ),
        ];

        for (actual_symbols, symbols) in expected.iter() {
            for sym in symbols {
                let result = actual_symbols.borrow();
                let result = result.resolve(&sym.name);

                assert!(result.is_some());
                assert_eq!(sym, &result.unwrap());
            }
        }
    }
}
