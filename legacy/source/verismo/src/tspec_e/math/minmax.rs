use super::*;

verus! {

pub fn min(x: u64, y: u64) -> (res: u64)
    ensures
        res as int === spec_min(x as int, y as int),
{
    if x < y {
        x
    } else {
        y
    }
}

pub fn max(x: u64, y: u64) -> (res: u64)
    ensures
        res as int === spec_max(x as int, y as int),
{
    if x > y {
        x
    } else {
        y
    }
}

} // verus!
