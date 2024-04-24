use super::bits_p::*;
use super::*;

verus! {

pub proof fn lemam_bit_or_mask_bound(val: u64, align: u64) -> (mask: u64)
    requires
        spec_bit64_is_shl_by_bits(align),
        val <= MAXU64!() - align,
    ensures
        mask == sub(align, 1),
        (val | mask) < MAXU64!(),
{
    let mask = sub(align, 1);
    assert((val | mask) < MAXU64!()) by (bit_vector)
        requires
            val <= sub(MAXU64!(), align),
            mask == sub(align, 1),
            spec_bit64_is_shl_by_bits(align),
    ;
    mask
}

seq_macro::seq!(N in 0..64 {
        verus! {
            pub proof fn lemma_bit_and_mod_rel(val: u64, align: u64)
            requires
                spec_bit64_is_shl_by_bits(align),
            ensures
                val % align == (val & sub(align, 1)),
            {
                #(
                    assert(val % BIT64!(N as u64) == (val & sub(BIT64!(N as u64), 1))) by(bit_vector);
                )*
            }
        }
        }
    );

pub proof fn proof_align_down(val: nat, align: nat) -> (ret: (u64, u64, u64))
    requires
        spec_bit64_is_pow_of_2(align as int),
        val as u64 == val,
    ensures
        ret.0 == sub(align as u64, 1),
        ret.1 == spec_pow2_to_bits(align as u64),
        ret.2 == val - val % align,
        ret.2 == val / align * align,
        ret.2 == (val as u64) >> ret.1 << ret.1,
        ret.2 == (val as u64) & (!ret.0),
{
    let bits: u64 = spec_pow2_to_bits(align as u64) as u64;
    let val64 = val as u64;
    let mask = sub(align as u64, 1);
    let ret = val - val % align;
    let align64 = BIT64!(bits);
    bit_shl64_pow2_auto();
    assert(val / align * align == val - val % align) by (nonlinear_arith)
        requires
            align != 0,
    ;
    assert(val64 / align as u64 == val / align) by (nonlinear_arith)
        requires
            align != 0,
            val == val64,
            align == align as u64,
    ;
    bit_rsh64_div_rel(val64, bits);
    bit_lsh64_mul_rel(val64 >> bits, bits);
    assert((val64 >> bits) << bits == val64 / align64 * align64);
    assert(val64 & !sub(BIT64!(bits), 1) == ((val64 >> bits) << bits)) by (bit_vector)
        requires
            bits < 64,
    ;
    (mask, bits, ret as u64)
}

pub proof fn proof_align_up(val: nat, align: nat) -> (ret: (u64, u64, u64, u64))
    requires
        spec_bit64_is_pow_of_2(align as int),
        val as u64 == val,
        val + align <= MAXU64!(),
    ensures
        ret.0 == sub(align as u64, 1),
        ret.1 == spec_pow2_to_bits(align as u64),
        ret.2 == if val % align != 0 {
            val + (align - val % align) as nat
        } else {
            val
        },
        ret.3 == val as u64 | ret.0,
        val % align != 0 ==> (ret.3 + 1) as u64 == ret.3 + 1,
        val as u64 & ret.0 == val % align,
        ret.2 == if val as u64 & ret.0 as u64 != 0 {
            add(ret.3, 1)
        } else {
            val as u64
        },
{
    let bits: u64 = spec_pow2_to_bits(align as u64) as u64;
    let val64 = val as u64;
    let align64 = align as u64;
    let mask = sub(align as u64, 1);
    let ret = val + (align - val % align);
    let tmp = val64 | mask;
    let ret2 = add(tmp, 1);
    bit_shl64_pow2_auto();
    assert(val / align * align == val - val % align) by (nonlinear_arith)
        requires
            align != 0,
    ;
    bit_rsh64_div_rel(val64, bits);
    lemma_bit_and_mod_rel(val64, align64);
    assert(val % align == (val64 % align64));
    lemam_bit_or_mask_bound(val64, align64);
    if val64 & mask != 0 {
        assert(add(val64, sub(align64, val64 & mask)) == ret2) by (bit_vector)
            requires
                align64 == 1u64 << bits,
                mask == sub(align64, 1),
                ret2 == add(tmp, 1),
                tmp == val64 | mask,
                bits < 64,
        ;
        (mask, bits, ret as u64, tmp)
    } else {
        (mask, bits, val as u64, tmp)
    }
}

pub open spec fn spec_align_up(val: int, align: int) -> int {
    let r = val % align;
    val + if r == 0 {
        0
    } else {
        align - r
    }
}

pub open spec fn spec_align_down(val: int, align: int) -> int {
    val - val % align
}

pub proof fn proof_align_is_aligned(val: int, align: int)
    requires
        align > 0,
        val >= 0,
    ensures
        spec_align_up(val, align) % align == 0,
        spec_align_down(val, align) % align == 0,
{
    let k = proof_div_mod_rel(val, align);
    let up = spec_align_up(val, align);
    let down = spec_align_down(val, align);
    assert(down == k * align);
    assert(up == k * align + align || up == k * align);
    assert(k * align + align == (k + 1) * align) by (nonlinear_arith);
    proof_mul_div_rel(k, align);
    proof_mul_div_rel(k + 1, align);
    proof_div_mod_rel(up, align);
    proof_div_mod_rel(down, align);
}

pub open spec fn spec_is_align_up_by_int(val: int, align: int, ret: int) -> bool {
    &&& ret % align == 0
    &&& ret == spec_align_up(val, align)
    &&& val <= ret < val + align
}

pub open spec fn spec_is_align_down_by_int(val: int, align: int, ret: int) -> bool {
    &&& (ret as int) == val as int - val as int % align as int
    &&& ret as int == (val as u64 >> spec_pow2_to_bits(align as u64)) << spec_pow2_to_bits(
        align as u64,
    )
    &&& (ret as int) % (align as int) == 0
}

pub open spec fn spec_valid_align(align: int) -> bool {
    //&&& (align as int) % BLOCK_SIZE!() == 0
    &&& spec_bit64_is_pow_of_2(align)
}

pub proof fn proof_modeq_propogation(a: int, b: int, c: int)
    requires
        b >= 1,
        c >= 1,
        a >= 0,
        a % b == 0,
        b % c == 0,
    ensures
        a % c == 0,
{
    let i = proof_div_mod_rel(a, b);
    let j = proof_div_mod_rel(b, c);
    proof_mul_exchange(i, j);
    proof_mul_exchange(i, b);
    proof_mul_exchange(j, c);
    proof_mul_exchange(j * i, c);
    let aa = proof_mul_div_rel(j * i, c);
    assert(a == b * i);
    assert(b == c * j);
    assert(a == c * j * i);
    proof_mul_dist(c, j, i);
    assert(aa == j * i * c);
    assert(a == aa);
    proof_div_mod_rel(a, c);
}

} // verus!
