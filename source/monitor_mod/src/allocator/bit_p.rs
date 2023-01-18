use super::*;

verus! {
    pub proof fn lemma_get_low_bits_via_bit_op(val: u64, align: u64) -> (ret: u64)
    requires
        spec_bit64_is_pow_of_2(align as int),
        (val & sub(align, 1) == 0),
    ensures
        ret == val & add(!val, 1),
        val != 0 ==> (ret >= align && spec_bit64_is_pow_of_2(ret as int)),
        val == 0 ==> ret == 0,
        val & sub(ret, 1) == 0,
        val & ret == ret,
    {
        bit_shl64_pow2_auto();
        let ret = val & add(!val, 1);
        assert(val & ret == ret) by(bit_vector)
        requires
            ret == val & add(!val, 1);
        assert(val & sub(ret, 1) == 0u64) by(bit_vector)
        requires
            ret == val & add(!val, 1);
        if val == 0 {
            assert(val & add(!val, 1) == 0u64) by(bit_vector)
            requires val == 0u64;
            assert(ret == 0);
        } else {
            assert(spec_bit64_is_shl_by_bits(ret)) by(bit_vector)
            requires
                ret == val & add(!val, 1),
                0 < val;
            assert(ret >= align) by(bit_vector)
            requires
                val & sub(align, 1) == 0u64,
                ret == val & add(!val, 1),
                spec_bit64_is_pow_of_2(align as int),
                0< val;
        }
        ret
    }

    #[verifier(external_body)]
    pub proof fn proof_buddy(current_addr: u64, current_bucket: u64, current_size: u64) -> (ret: u64)
    requires
        current_bucket < 63,
        current_addr % current_size == 0,
        current_size == (1u64 << current_bucket)
    ensures
        ret ==  current_addr ^ current_size,
        ret == current_addr + current_size || ret + current_size == current_addr,
        current_addr as int % (current_size * 2) == 0 ==> ret == current_addr + current_size,
        current_addr as int % (current_size * 2) != 0 ==> ret + current_size == current_addr,
        ret % (1u64 << add(current_bucket, 1)) == 0,
        current_size * 2 == (1u64 << add(current_bucket, 1)),
        current_size > 0,
    {
        current_addr ^ (1u64 << current_bucket)
    }
}
