// math -> sec_lib;
// math -> size
// size -> array
// size -> stream
#[macro_use]
mod math;
mod cast;
mod constant;
mod default;
mod fmap;
mod isconst;
mod macros;
mod ops;
mod range_set;
#[macro_use]
mod security;
mod fnspec;
#[macro_use]
mod integer;
pub mod map_lib;
mod seqlib;
mod setlib;
mod size_s;
mod stream;
mod wellformed;

//use builtin::*;
pub use builtin_macros::*;
pub use cast::*;
pub use default::*;
pub use fmap::FMap;
pub use fnspec::*;
pub use integer::*;
pub use isconst::*;
pub use math::*;
pub use ops::*;
pub use range_set::*;
pub use security::*;
pub use seqlib::*;
pub use setlib::*;
pub use size_s::*;
pub use stream::basic::*;
pub use stream::{Byte, ByteStream, Stream, *};
pub use verismo_macro::*;
pub use verismo_verus::*;
pub use vstd::pervasive::{affirm, arbitrary, proof_from_false, spec_affirm, unreached};
pub use vstd::prelude::*;
pub use vstd::slice::SliceAdditionalSpecFns;
pub use vstd::std_specs::option::OptionAdditionalFns;
pub use vstd::std_specs::result::ResultAdditionalSpecFns;
pub use vstd::string::{StrSlice, String, *};
pub use vstd::view::*;
pub use wellformed::*;

verus! {

// const
#[verifier(inline)]
pub open spec fn spec_unused<T>() -> T {
    arbitrary()
}

} // verus!
verus! {

#[is_variant]
pub enum ResultOrErr<RetValue, ErrorID> {
    Ok(RetValue),
    Error(ErrorID),
}

impl<RetValue, ErrorID> ResultOrErr<RetValue, ErrorID> {
    pub open spec fn with_when_err(&self, err_ret: RetValue) -> ResultWithErr<RetValue, ErrorID> {
        match *self {
            ResultOrErr::Ok(ret) => ResultWithErr::Ok(ret),
            ResultOrErr::Error(err) => ResultWithErr::Error(err_ret, err),
        }
    }

    pub open spec fn to_result(&self) -> RetValue {
        match self {
            ResultOrErr::Ok(ret) => *ret,
            ResultOrErr::Error(ret) => spec_unused(),
        }
    }
}

} // verus!
verus! {

#[is_variant]
pub enum ResultWithErr<RetValue, ErrorID> {
    Ok(RetValue),
    Error(RetValue, ErrorID),
}

impl<RetValue, ErrorID> ResultWithErr<RetValue, ErrorID> {
    verus! {
        pub open spec fn with_err<ET2>(&self, err: ET2) -> ResultWithErr<RetValue, ET2> {
            match self {
                ResultWithErr::Ok(ret) => ResultWithErr::Error(*ret, err),
                ResultWithErr::Error(ret, olderr) => ResultWithErr::Error(*ret, err),
            }
        }

        pub open spec fn replace_err<ET2>(&self, err: ET2) -> ResultWithErr<RetValue, ET2> {
            match self {
                ResultWithErr::Ok(ret) => ResultWithErr::Ok(*ret),
                ResultWithErr::Error(ret, olderr) => ResultWithErr::Error(*ret, err),
            }
        }

        pub open spec fn with_ret<RT2>(&self, ret: RT2) -> ResultWithErr<RT2, ErrorID> {
            match self {
                ResultWithErr::Ok(_) => ResultWithErr::Ok(ret),
                ResultWithErr::Error(_, err) => ResultWithErr::Error(ret, *err),
            }
        }

        pub open spec fn to_result(&self) -> RetValue {
            match self {
                ResultWithErr::Ok(ret) => *ret,
                ResultWithErr::Error(ret, _) => *ret,
            }
        }

        pub open spec fn to_err(&self) -> ErrorID {
            match self {
                ResultWithErr::Ok(ret) => spec_unused(),
                ResultWithErr::Error(ret, err) => *err,
            }
        }
    }
}

} // verus!
