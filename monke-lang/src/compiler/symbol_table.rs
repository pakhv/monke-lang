use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use crate::builtins::BUILTINS;

#[derive(Debug, PartialEq, Clone)]
pub enum SymbolScope {
    Global,
    Local,
    Builtin,
    Free,
    Function,
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
    pub free_symbols: Vec<Symbol>,
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
            free_symbols: vec![],
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

    pub fn resolve(&mut self, name: &str) -> Option<Symbol> {
        let result = self.store.get(name);

        match result {
            Some(symbol) => Some(symbol.clone()),
            None => match &self.outer.clone() {
                Some(outer) => match outer.borrow_mut().resolve(name) {
                    Some(outer_result) => {
                        if outer_result.scope == SymbolScope::Global
                            || outer_result.scope == SymbolScope::Builtin
                        {
                            return Some(outer_result);
                        }

                        let free = self.define_free(outer_result);
                        Some(free)
                    }
                    None => None,
                },
                None => None,
            },
        }
    }

    pub fn new_enclosed(outer: SymbolTableRef) -> SymbolTableRef {
        let new_table = SymbolTable::new();
        new_table.borrow_mut().outer = Some(outer);

        new_table
    }

    pub fn define_builtin(&mut self, index: usize, name: String) -> Symbol {
        let symbol = Symbol {
            index,
            name: name.clone(),
            scope: SymbolScope::Builtin,
        };

        self.store.insert(name, symbol.clone());
        symbol
    }

    pub fn populate_symbol_table_with_builtins(&mut self) {
        for (idx, &name) in BUILTINS.iter().enumerate() {
            self.define_builtin(idx, name.to_string());
        }
    }

    pub fn define_free(&mut self, original: Symbol) -> Symbol {
        self.free_symbols.push(original.clone());

        let symbol = Symbol {
            name: original.name.clone(),
            index: self.free_symbols.len() - 1,
            scope: SymbolScope::Free,
        };

        self.store.insert(original.name, symbol.clone());
        symbol
    }

    pub fn define_function_name(&mut self, name: String) -> Symbol {
        let symbol = Symbol {
            name: name.clone(),
            index: 0,
            scope: SymbolScope::Function,
        };

        self.store.insert(name, symbol.clone());
        symbol
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
            let mut result = table.borrow_mut();
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
            let mut result = local.borrow_mut();
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
                Rc::clone(&first_local),
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
                Rc::clone(&second_local),
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
                let mut result = actual_symbols.borrow_mut();
                let result = result.resolve(&sym.name);

                assert!(result.is_some());
                assert_eq!(sym, &result.unwrap());
            }
        }
    }

    #[test]
    fn define_resolve_builtins_test() {
        let global = SymbolTable::new();
        let first_local = SymbolTable::new_enclosed(Rc::clone(&global));
        let second_local = SymbolTable::new_enclosed(Rc::clone(&first_local));

        let expected = [
            Symbol {
                name: String::from("a"),
                scope: SymbolScope::Builtin,
                index: 0,
            },
            Symbol {
                name: String::from("b"),
                scope: SymbolScope::Builtin,
                index: 1,
            },
            Symbol {
                name: String::from("c"),
                scope: SymbolScope::Builtin,
                index: 2,
            },
            Symbol {
                name: String::from("d"),
                scope: SymbolScope::Builtin,
                index: 3,
            },
        ];

        for (idx, val) in expected.iter().enumerate() {
            global.borrow_mut().define_builtin(idx, val.name.clone());
        }

        for table in [global, first_local, second_local] {
            for sym in &expected {
                let result = table.borrow_mut().resolve(&sym.name);
                assert!(result.is_some());
                assert_eq!(&result.unwrap(), sym);
            }
        }
    }

    #[test]
    fn resolve_free_test() {
        let global = SymbolTable::new();
        global.borrow_mut().define(String::from("a"));
        global.borrow_mut().define(String::from("b"));

        let first_local = SymbolTable::new_enclosed(Rc::clone(&global));
        first_local.borrow_mut().define(String::from("c"));
        first_local.borrow_mut().define(String::from("d"));

        let second_local = SymbolTable::new_enclosed(Rc::clone(&first_local));
        second_local.borrow_mut().define(String::from("e"));
        second_local.borrow_mut().define(String::from("f"));

        let expected = [
            (
                first_local,
                vec![
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
                vec![],
            ),
            (
                second_local,
                vec![
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
                        scope: SymbolScope::Free,
                        index: 0,
                    },
                    Symbol {
                        name: String::from("d"),
                        scope: SymbolScope::Free,
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
                vec![
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
        ];

        for (table, symbols, free_symbols) in expected {
            for sym in &symbols {
                let result = table.borrow_mut().resolve(&sym.name);
                assert!(result.is_some());
                assert_eq!(&result.unwrap(), sym);
            }

            assert_eq!(free_symbols.len(), table.borrow().free_symbols.len());

            for (exp_sym, actual_sym) in free_symbols.iter().zip(table.borrow().free_symbols.iter())
            {
                assert_eq!(exp_sym, actual_sym);
            }
        }
    }

    #[test]
    fn resolve_unresolvable_free_test() {
        let global = SymbolTable::new();
        global.borrow_mut().define(String::from("a"));

        let first_local = SymbolTable::new_enclosed(Rc::clone(&global));
        first_local.borrow_mut().define(String::from("c"));

        let second_local = SymbolTable::new_enclosed(Rc::clone(&first_local));
        second_local.borrow_mut().define(String::from("e"));
        second_local.borrow_mut().define(String::from("f"));

        let expected = [
            Symbol {
                name: String::from("a"),
                scope: SymbolScope::Global,
                index: 0,
            },
            Symbol {
                name: String::from("c"),
                scope: SymbolScope::Free,
                index: 0,
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
        ];

        for sym in expected {
            let result = second_local.borrow_mut().resolve(&sym.name);
            assert!(result.is_some());
            assert_eq!(result.unwrap(), sym);
        }

        let expected_unresolvable = vec![String::from("b"), String::from("d")];

        for name in expected_unresolvable {
            assert!(second_local.borrow_mut().resolve(&name).is_none());
        }
    }

    #[test]
    fn define_and_resolve_function_name_test() {
        let global = SymbolTable::new();
        global.borrow_mut().define_function_name(String::from("a"));

        let expected = Symbol {
            name: String::from("a"),
            scope: SymbolScope::Function,
            index: 0,
        };

        let result = global.borrow_mut().resolve(&expected.name);
        assert!(result.is_some());
        assert_eq!(expected, result.unwrap());
    }

    #[test]
    fn shadowing_function_name_test() {
        let global = SymbolTable::new();
        global.borrow_mut().define_function_name(String::from("a"));
        global.borrow_mut().define(String::from("a"));

        let expected = Symbol {
            name: String::from("a"),
            scope: SymbolScope::Global,
            index: 0,
        };

        let result = global.borrow_mut().resolve(&expected.name);
        assert!(result.is_some());
        assert_eq!(expected, result.unwrap());
    }
}
