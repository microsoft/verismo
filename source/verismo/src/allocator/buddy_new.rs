use super::buddy::ORDER_USIZE;
use super::*;
use crate::linkedlist::LinkedList;

seq_macro::seq!(N in 0..32 {
verus!{
        //impl Array<LinkedList<()>, ORDER_USIZE> {
        #[verifier(external_body)]
        pub const fn new_array_linked_list32() -> (ret: Array<LinkedList<()>, ORDER_USIZE>)
        ensures
        ret@.len() == ORDER_USIZE as nat,
        forall |i: int| 0 <= i < ret@.len() as int ==> ret@[i]@.len() == 0,
        forall |i: int| 0 <= i < ret@.len() as int ==> ret@[i].inv(),
        //forall |i: int| 0 <= i < ret@.len() as int ==> ret@[i].is_Some(),
        forall |i: int| 0 <= i < ret@.len() as int ==> ret@[i].is_constant(),
        ret.is_constant()
        {
        Array{array: [#(LinkedList::new(),)*]}
        }
}
});
