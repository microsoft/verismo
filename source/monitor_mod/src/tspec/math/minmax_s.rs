use super::*;
verus! {
    pub open spec fn spec_max(a: int, b: int) -> int {
        if a > b {a} else {b}
    }

    pub open spec fn spec_min(a: int, b: int) -> int {
        if a > b {b} else {a}
    }
}
