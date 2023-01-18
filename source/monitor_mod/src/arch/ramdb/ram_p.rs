use super::ram_s::*;
use super::*;
use crate::arch::addr_s::*;
use crate::arch::crypto::encdec::SpecEncrypt;
use crate::arch::crypto::SymKey;
use crate::arch::entities::ASID;
use crate::tspec::*;
use crate::*;

verus! {
impl RamDB {
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_ram_len1(&self)
    ensures
        #[trigger] self.data.len() == VM_MEM_SIZE!(),
    {}

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_ram_len2(&self, spa: SPA)
    ensures
        #[trigger]spa.as_int() < #[trigger]self.data.len(),
    {}

    pub proof fn lemma_write_inv(&self, asid: ASID, spmem: SPMem, bytes: Seq<Byte>)
    requires
        self.inv()
    ensures
        self.write_raw(asid, spmem, bytes).inv(),
    {
        reveal(RamDB::inv);
        let new = self.write_raw(asid, spmem, bytes);
        assert forall |spa: SPA|
            (0 <= spa.as_int() < self.spec_data().len())
        implies
            (#[trigger] new.data[spa.as_int()]).key.key.1 == idx(spa)
        by {
            assert(0 <= spa.as_int() < self.spec_data().len());
            self.lemma_write_raw(spa, asid, spmem, bytes);
            assert(new.data[spa.as_int()] === self.to_write(spa, asid, spmem, bytes));
            assert((self.data[spa.as_int()]).key.key.1 == idx(spa));
        };
    }

    pub proof fn lemma_write_raw(&self, spa: SPA, asid: ASID, spmem: SPMem, bytes: Seq<Byte>)
    requires
        0 <= spa.as_int() < self.spec_data().len()
    ensures
        self.write_raw(asid, spmem, bytes).spec_data()[spa.as_int()] === self.to_write(spa, asid, spmem, bytes)
    {
        reveal(RamDB::write_raw);
    }


    pub proof fn lemma_write_change_byte(&self, asid: ASID, spmem: SPMem, bytes: Seq<Byte>, rspa: SPA)
    requires
        spmem.last().as_int() < self.len(),
        spmem.is_valid(),
        spmem.contains(rspa),
        bytes.len() == spmem.len(),
    ensures
        self.write_raw(asid, spmem, bytes).read_one_byte(asid, rspa) === bytes[rspa.as_int() - spmem.first().as_int()]
    {
        let crypto_mask: Byte = self.crypto_mask[self.spec_write_count()].get_mask();
        let new = self.write_raw(asid, spmem, bytes);
        let read_byte = new.read_one_byte(asid, rspa);
        let k = rspa.as_int() - spmem.first().as_int();
        assert(0 <= k < spmem.len());
        assert(0 <= rspa.as_int() < self.len());
        self.lemma_write_raw(rspa, asid, spmem, bytes);
        assert(new.data[rspa.as_int()] ===
        SymKey{key: (asid, idx(spmem[k]))}.encrypt(
            bytes[k],
            crypto_mask)
        );
        assert(read_byte === SymKey{key: (asid, idx(spmem[k]))}.decrypt(new.data[spmem[k].as_int()]));
        assert(bytes[k] === read_byte);
    }

    pub proof fn lemma_write_unchange_byte(&self, asid: ASID, spmem: SPMem, bytes: ByteStream, rspa: SPA)
    requires
        spmem.is_valid(),
        !spmem.contains(rspa),
        spmem.last().as_int() < self.len(),
        bytes.len() == spmem.len(),
        rspa.as_int() < self.len(),
    ensures
        self.write_raw(asid, spmem, bytes).read_one_byte(asid, rspa) === self.read_one_byte(asid, rspa)
    {
        reveal(RamDB::write_raw);
        let new = self.write_raw(asid, spmem, bytes);
        if !memrange_contains_block(spmem, idx(rspa)) {
            assert(self.to_write(rspa, asid, spmem, bytes) === self.spec_data()[rspa.as_int()]);
            assert(self.to_write(SPA::new(rspa.as_int()), asid, spmem, bytes) === self.write_raw(asid, spmem, bytes).spec_data()[rspa.as_int()]);
        }

    }

    pub proof fn lemma_write_unchange_byte_any_enc(&self, asid: ASID, spmem: SPMem, bytes: ByteStream, rasid: ASID, rspa: SPA)
    requires
        spmem.is_valid(),
        spmem.last().as_int() < self.len(),
        rspa.as_int() < self.len(),
        !memrange_contains_block(spmem, idx(rspa)),
        bytes.len() == spmem.len(),
    ensures
        self.write_raw(asid, spmem, bytes).read_one_byte(rasid, rspa) === self.read_one_byte(rasid, rspa)
    {
        reveal(RamDB::write_raw);
        let new = self.write_raw(asid, spmem, bytes);
        assert(self.to_write(rspa, asid, spmem, bytes) == self.data[rspa.as_int()]);
        assert(self.to_write(rspa, asid, spmem, bytes) == new.data[rspa.as_int()]);
    }

    pub proof fn proof_read_write(&self, asid: ASID, spmem: SPMem, bytes: ByteStream)
    requires
        spmem.is_valid(),
        spmem.last().as_int() < self.len(),
        bytes.len() == spmem.len(),
    ensures
        self.write_raw(asid, spmem, bytes).read_bytes_by_asid(asid, spmem) === bytes,
    {
        reveal(RamDB::read_bytes_by_asid);
        reveal(RamDB::write_raw);
        let new = self.write_raw(asid, spmem, bytes);
        let read_bytes = new.read_bytes_by_asid(asid, spmem);
        let crypto_mask: Byte = self.crypto_mask[self.spec_write_count()].get_mask();
        assert(
            new.data === Stream::new(
                self.data.len(),
                |i: int| self.to_write(SPA::new(i), asid, spmem, bytes)
            )
        );
        assert(bytes.len() === spmem.len());
        assert forall | k|
            0 <= k < bytes.len()
        implies
            (bytes[k] === read_bytes[k])
        by {
            let i = spmem[k].as_int();
            assert(k == i - spmem[0].as_int());
            assert(spmem[k].to_page() === spmem.to_page());
            assert(0 <= k < spmem.len());
            assert(spmem.contains(spmem[k]));
            self.lemma_write_change_byte(asid, spmem, bytes, spmem[k]);
        }
        assert(bytes=~~=(read_bytes));
    }

    //#[verifier(external_body)]
    pub proof fn proof_read_write_no_change(&self, asid: ASID, spmem: SPMem, data: ByteStream, rspmem: SPMem)
    requires
        self.inv(),
        spmem.is_valid(),
        spmem.last().as_int() < self.len(),
        rspmem.is_valid(),
        rspmem.last().as_int() < self.len(),
        data.len() == spmem.len(),
        rspmem.disjoint(spmem),
    ensures
        self.write_raw(asid, spmem, data).read_bytes_by_asid(asid, rspmem) === self.read_bytes_by_asid(asid, rspmem),
    {
        reveal(RamDB::inv);
        let new = self.write_raw(asid, spmem, data);
        reveal(RamDB::read_bytes_by_asid);
        let bytes = Stream::new(
            rspmem.len(),
            |i: int| self.read_one_byte(asid, rspmem[i])
        );
        let new_bytes = Stream::new(
            rspmem.len(),
            |i: int| new.read_one_byte(asid, rspmem[i])
        );
        assert forall |s: int|
            0 <= s < rspmem.len()
        implies
            bytes[s] === new_bytes[s]
        by {
            self.lemma_write_unchange_byte(asid, spmem, data, rspmem[s]);
        }
        assert(new_bytes === bytes) by {
            assert(new_bytes=~~=(bytes));
        }
    }
}
}
