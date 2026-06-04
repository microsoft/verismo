pub mod basic;

use vstd::prelude::*;

use super::size_s::*;
use super::*;

pub type Byte = u8;
pub type EncUnit = u128;
pub use basic::*;
pub type Stream<T> = Seq<T>;
pub type ByteStream = Seq<u8>;

verus! {

impl VSpecShr<nat, ByteStream> for ByteStream {
    #[verifier(inline)]
    open spec fn spec_shr(self, rhs: nat) -> Self {
        self.subrange(rhs as int, self.len() - rhs)
    }
}

pub open spec fn stream_to_data<T: VTypeCast<ByteStream>>(s: ByteStream) -> T {
    choose|ret: T| ret.vspec_cast_to() =~~= s
}

#[verifier(opaque)]
pub open spec fn stream_from_data<T: VTypeCast<ByteStream>>(data: T) -> ByteStream {
    data.vspec_cast_to()
}

pub proof fn lemma_from_data<T: VTypeCast<ByteStream>>(data: T) -> (ret: ByteStream)
    ensures
        ret === stream_from_data(data),
        stream_from_data(stream_to_data::<T>(ret)) === ret,
{
    reveal(stream_from_data);
    stream_from_data(data)
}

} // verus!
