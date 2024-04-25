use super::*;
use crate::*;

verus! {

#[verifier(inline)]
pub open spec fn bool_to_stream(data: bool) -> ByteStream {
    u8_to_stream(
        if data {
            1u8
        } else {
            0u8
        },
    )
}

#[verifier(inline)]
pub open spec fn char_to_stream(data: char) -> ByteStream {
    u8_to_stream(data as u8)
}

//#[verifier(inline)]
pub open spec fn u8_to_stream(data: u8) -> ByteStream {
    Seq::new(
        1,
        |i|
            if i == 0 {
                data
            } else {
                0u8
            },
    )
}

#[verifier(inline)]
pub open spec fn ghost_to_stream<T>(data: Ghost<T>) -> ByteStream {
    Stream::new(0, |i| 0u8)
}

#[verifier(inline)]
pub open spec fn u16_to_stream(data: u16) -> ByteStream {
    (u8_to_stream(data as u8) + u8_to_stream((data / 0x100) as u8))
}

#[verifier(inline)]
pub open spec fn u32_to_stream(data: u32) -> ByteStream {
    (u16_to_stream(data as u16).add(u16_to_stream((data / 0x10000) as u16)))
}

#[verifier(inline)]
pub open spec fn u64_to_stream(data: u64) -> ByteStream {
    u32_to_stream(data as u32).add(u32_to_stream((data / 0x1_0000_0000) as u32))
}

#[verifier(inline)]
pub open spec fn u128_to_stream(data: u128) -> ByteStream {
    u64_to_stream(data as u64).add(u64_to_stream((data / 0x10000_0000) as u64))
}

#[verifier(inline)]
pub open spec fn usize_to_stream(data: usize) -> ByteStream {
    //if arch_word_bits() == 8 {
    u64_to_stream(data as u64)
    //} else {
    //    u32_to_stream(data as u32)
    //}

}

#[verifier(inline)]
pub open spec fn bool_from_stream(data: ByteStream) -> bool {
    data[0] != 0
}

//#[verifier(inline)]
pub open spec fn char_from_stream(data: ByteStream) -> char;

//#[verifier(inline)]
pub open spec fn u8_from_stream(data: ByteStream) -> u8 {
    data[0]
}

#[verifier(inline)]
pub open spec fn u16_from_stream(data: ByteStream) -> u16 {
    (u8_from_stream(data.subrange(0, 1)) + u8_from_stream(data.subrange(1, 2)) * 0x100) as u16
}

#[verifier(inline)]
pub open spec fn u32_from_stream(data: ByteStream) -> u32 {
    (u16_from_stream(data.subrange(0, 2)) + u16_from_stream(data.subrange(2, 4)) * 0x10000) as u32
}

#[verifier(inline)]
pub open spec fn u64_from_stream(data: ByteStream) -> u64 {
    (u32_from_stream(data.subrange(0, 4)) + u32_from_stream(data.subrange(4, 8))
        * 0x10000_0000) as u64
}

#[verifier(inline)]
pub open spec fn u128_from_stream(data: ByteStream) -> u128 {
    (u64_from_stream(data.subrange(0, 8)) + u64_from_stream(data.subrange(8, 16))
        * 0x10000_0000_0000_0000) as u128
}

#[verifier(inline)]
pub open spec fn usize_from_stream(data: ByteStream) -> usize {
    //if arch_word_bits() == 8 {
    u64_from_stream(data) as usize
    //} else {
    //    u32_from_stream(data as u32)
    //}

}

pub proof fn proof_u64_non_zero(data: u64)
    requires
        forall|i| 0 <= i < 8 ==> #[trigger] (u64_to_stream(data)[i]) == 0,
    ensures
        data == 0,
{
    let l = data as u32;
    let h = (data / 0x10000_0000) as u32;
    if data != 0 {
        assert forall|i| 0 <= i < 4 implies #[trigger] (u32_to_stream(l)[i]) == 0 by {
            assert(u64_to_stream(data)[i] == 0);
        }
        proof_u32_non_zero(l);
        assert forall|i| 0 <= i < 4 implies #[trigger] (u32_to_stream(h)[i]) == 0 by {
            assert(u64_to_stream(data)[i + 4] == 0);
        }
        proof_u32_non_zero(h);
    }
}

pub proof fn proof_u32_non_zero(data: u32)
    requires
        forall|i| 0 <= i < 4 ==> #[trigger] (u32_to_stream(data)[i]) == 0,
    ensures
        data == 0,
{
    let l = data as u16;
    let h = (data / 0x10000) as u16;
    assert forall|i| 0 <= i < 2 implies #[trigger] (u16_to_stream(l)[i]) == 0 by {
        assert(u32_to_stream(data)[i] == 0);
    }
    proof_u16_non_zero(l);
    assert forall|i| 0 <= i < 2 implies #[trigger] (u16_to_stream(h)[i]) == 0 by {
        assert(u32_to_stream(data)[i + 2] == 0);
    }
    proof_u16_non_zero(h);
}

pub proof fn proof_u16_non_zero(data: u16)
    requires
        forall|i| 0 <= i < 2 ==> (#[trigger] u16_to_stream(data)[i]) == 0,
    ensures
        data == 0,
{
    let l = data as u8;
    let h = (data / 0x100) as u8;
    assert(u16_to_stream(data)[0] == 0);
    assert(u16_to_stream(data)[1] == 0);
    proof_u8_non_zero(l);
    proof_u8_non_zero(h);
}

pub proof fn proof_u8_non_zero(data: u8)
    requires
        u8_to_stream(data)[0] == 0,
    ensures
        data == 0,
{
}

} // verus!
