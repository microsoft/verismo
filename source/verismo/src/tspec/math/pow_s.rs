use vstd::prelude::*;

use super::*;

verus! {

#[verifier(inline)]
pub open spec fn spec_pow2_to_bits(val: u64) -> u64 {
    choose|ret: u64| BIT64!(ret) == val && 0 <= ret < 64
}

pub open spec fn spec_int_pow2(offset: int) -> int
    recommends
        offset >= 0,
{
    spec_nat_pow2(offset as nat)
}

pub open spec fn spec_nat_pow2(e: nat) -> int
    decreases e,
{
    if e == 0 {
        1
    } else {
        2 * spec_nat_pow2((e - 1) as nat)
    }
}

seq_macro::seq!(N in 0..64 {
        verus!{
            #[verifier(inline)]
            pub open spec fn spec_bit64_is_pow_of_2(val: int) -> bool {
                #(
                    ||| val == POW2!(N)
                )*
            }
        }
    }
    );

seq_macro::seq!(N in 0..64 {
        verus!{
            #[verifier(inline)]
            pub open spec fn spec_bit64_is_shl_by_bits(val: u64) -> bool {
                #(
                    ||| val == BIT64!(N as u64)
                )*
            }
        }
    }
    );

} // verus!
