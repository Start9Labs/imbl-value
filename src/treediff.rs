use std::fmt;
use std::mem;
use std::sync::Arc;

use crate::{in_order_map as map, InOMap as Map, Value as ImblValue};
use imbl::Vector;
use treediff::{Mutable, Value};

/// A representation of all key types typical Value types will assume.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum Key {
    /// An array index
    Index(usize),
    /// A string index for mappings
    String(Arc<String>),
}

impl fmt::Display for Key {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Key::String(ref v) => v.fmt(f),
            Key::Index(ref v) => v.fmt(f),
        }
    }
}

impl Value for ImblValue {
    type Key = Key;
    type Item = ImblValue;
    fn items<'a>(&'a self) -> Option<Box<dyn Iterator<Item = (Self::Key, &'a Self::Item)> + 'a>> {
        match *self {
            ImblValue::String(_) | ImblValue::Number(_) | ImblValue::Bool(_) | ImblValue::Null => {
                None
            }
            ImblValue::Array(ref inner) => Some(Box::new(
                inner.iter().enumerate().map(|(i, v)| (Key::Index(i), v)),
            )),
            ImblValue::Object(ref inner) => Some(Box::new(
                inner.iter().map(|(s, v)| (Key::String(s.clone()), v)),
            )),
        }
    }
}

impl Mutable for ImblValue {
    type Key = Key;
    type Item = ImblValue;

    fn set(&mut self, keys: &[Self::Key], v: &Self::Item) {
        if keys.is_empty() {
            *self = v.clone();
        } else {
            let mut c = self;
            let last_key_index = keys.len() - 1;
            let object_or_value = |index| {
                if index == last_key_index {
                    v.clone()
                } else {
                    ImblValue::Object(Map::new())
                }
            };
            fn runup_array_or_value<'a>(
                array: &'a mut Vector<ImblValue>,
                target_index: usize,
                key_index: usize,
                last_key_index: usize,
                v: &ImblValue,
            ) -> &'a mut ImblValue {
                for _ in array.len()..target_index {
                    array.push_back(ImblValue::Null);
                }
                let value = if key_index == last_key_index {
                    v.clone()
                } else {
                    ImblValue::Null
                };
                if target_index == array.len() {
                    array.push_back(value);
                } else {
                    array[target_index] = value;
                }
                &mut array[target_index]
            }
            for (i, k) in keys.iter().enumerate() {
                c = match *k {
                    Key::String(ref k) => match { c } {
                        &mut ImblValue::Object(ref mut obj) => match obj.entry(k.clone()) {
                            map::Entry::Vacant(e) => e.insert(object_or_value(i)),
                            map::Entry::Occupied(e) => {
                                if i == last_key_index {
                                    *e.into_mut() = v.clone();
                                    return;
                                } else {
                                    e.into_mut()
                                }
                            }
                        },
                        c @ &mut ImblValue::String(_)
                        | c @ &mut ImblValue::Number(_)
                        | c @ &mut ImblValue::Bool(_)
                        | c @ &mut ImblValue::Null
                        | c @ &mut ImblValue::Array(_) => {
                            drop(mem::replace(
                                c,
                                ImblValue::Object({
                                    let mut o = Map::new();
                                    o.insert(k.clone(), object_or_value(i));
                                    o
                                }),
                            ));
                            if i == last_key_index {
                                return;
                            }
                            match c {
                                ImblValue::Object(ref mut obj) => {
                                    obj.get_mut(k.as_str()).expect("previous insertion")
                                }
                                _ => unreachable!(),
                            }
                        }
                    },
                    Key::Index(idx) => match { c } {
                        &mut ImblValue::Array(ref mut a) => {
                            runup_array_or_value(a, idx, i, last_key_index, v)
                        }
                        c @ &mut ImblValue::String(_)
                        | c @ &mut ImblValue::Number(_)
                        | c @ &mut ImblValue::Bool(_)
                        | c @ &mut ImblValue::Null
                        | c @ &mut ImblValue::Object(_) => {
                            let mut a = Vector::new();
                            runup_array_or_value(&mut a, idx, i, last_key_index, v);
                            drop(mem::replace(c, ImblValue::Array(a)));
                            if i == last_key_index {
                                return;
                            }
                            match c {
                                ImblValue::Array(ref mut a) => {
                                    a.get_mut(idx).expect("previous insertion")
                                }
                                _ => unreachable!(),
                            }
                        }
                    },
                }
            }
        }
    }

    fn remove(&mut self, keys: &[Self::Key]) {
        let mut c = self;
        let last_key_index = keys.len().checked_sub(1).expect("at least one key");
        for (i, k) in keys.iter().enumerate() {
            c = match *k {
                Key::String(ref k) => match { c } {
                    ImblValue::Object(ref mut obj) => {
                        if i == last_key_index {
                            obj.remove(k);
                            return;
                        } else {
                            match obj.get_mut(k.as_str()) {
                                Some(json) => json,
                                None => return,
                            }
                        }
                    }
                    _ => return,
                },
                Key::Index(idx) => match { c } {
                    ImblValue::Array(ref mut a) => {
                        if i == last_key_index {
                            a.remove(idx);
                            return;
                        } else {
                            match a.get_mut(idx) {
                                Some(json) => json,
                                None => return,
                            }
                        }
                    }
                    _ => return,
                },
            }
        }
    }
}
