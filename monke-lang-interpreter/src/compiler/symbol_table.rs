use std::collections::HashMap;

#[derive(Debug, PartialEq, Clone)]
pub enum SymbolScope {
    Global,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Symbol {
    pub name: String,
    pub scope: SymbolScope,
    pub index: usize,
}

#[derive(Debug, Clone)]
pub struct SymbolTable {
    pub store: HashMap<String, Symbol>,
    pub num_definitions: usize,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            num_definitions: 0,
        }
    }

    pub fn define(&mut self, name: String) -> Symbol {
        let symbol = Symbol {
            name: name.clone(),
            index: self.num_definitions,
            scope: SymbolScope::Global,
        };

        self.store.insert(name, symbol.clone());
        self.num_definitions += 1;

        symbol
    }

    pub fn resolve(&self, name: &str) -> Option<&Symbol> {
        self.store.get(name)
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

        let mut table = SymbolTable::new();
        let a = table.define(String::from("a"));
        let b = table.define(String::from("b"));

        assert_eq!(expected["a"], a);
        assert_eq!(expected["b"], b);
    }

    #[test]
    fn resolve_global_test() {
        let mut table = SymbolTable::new();
        table.define(String::from("a"));
        table.define(String::from("b"));

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
            let result = table.resolve(name);

            assert!(result.is_some());
            assert_eq!(symbol, result.unwrap());
        }
    }
}
