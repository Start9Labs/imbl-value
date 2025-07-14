use proptest::prelude::{Arbitrary, BoxedStrategy, Strategy};
use proptest_derive::Arbitrary;
use yasi::InternedString;

use crate::{InOMap, Value};

pub fn number_strategy() -> BoxedStrategy<Value> {
    #[derive(Debug, Arbitrary)]
    enum Number {
        PosInt(u64),
        NegInt(i64),
        Float(f64),
    }
    Number::arbitrary()
        .prop_map::<serde_json::Number, _>(|n| match n {
            Number::PosInt(a) => a.into(),
            Number::NegInt(a) => a.into(),
            Number::Float(a) => {
                serde_json::Number::from_f64(a).unwrap_or(serde_json::Number::from(0))
            }
        })
        .prop_map(Value::Number)
        .boxed()
}

pub fn array_strategy() -> BoxedStrategy<Value> {
    imbl::proptest::vector(Value::arbitrary(), 0..20)
        .prop_map(Value::Array)
        .boxed()
}

pub fn object_strategy() -> BoxedStrategy<Value> {
    imbl::proptest::vector(
        <(String, Value)>::arbitrary().prop_map(|(k, v)| (InternedString::intern(k), v)),
        0..20,
    )
    .prop_map(InOMap::from)
    .prop_map(Value::Object)
    .boxed()
}
