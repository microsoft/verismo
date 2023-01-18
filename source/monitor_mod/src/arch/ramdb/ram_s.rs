use super::*;
use crate::arch::addr_s::*;
use crate::arch::crypto::encdec::SpecEncrypt;
use crate::arch::crypto::*;
use crate::arch::entities::*;
use crate::tspec::*;
use crate::*;

crate::macro_const_int! {
    pub const MEM_UNIT_SIZE: u64 = 16u64;
}

verus! {
pub open spec fn idx2(spa_val: int) -> int{
    spa_val / (MEM_UNIT_SIZE as int)
}

pub open spec fn idx(spa: SPA) -> int{
    idx2(spa.as_int())
}

pub open spec fn memrange_contains_block(range: SpecMem<SysPhy>, i: int) -> bool
{
    &&& idx(range.first()) <= i
    &&& idx(range.last()) >= i
}

impl RamDB {
    pub open spec fn len(&self) -> nat {
        self.data.len()
    }

    #[verifier(opaque)]
    pub open spec fn inv(&self) -> bool {
        forall |spa: SPA| (0 <= spa.as_int() <  self.spec_data().len()) ==> (#[trigger] self.data[spa.as_int()]).key.key.1 == idx(spa)
    }


    /// The encryption of data is done with a 128-bit key in a mode which
    /// utilizes an additional physical address-based tweak to protect
    /// against cipher-text block moveattacks
    pub open spec fn write<T: VTypeCast<Seq<u8>>>(&self, asid: ASID, spa: SPMem, data: T) -> Self
    {
        let bytes = stream_from_data(data).subrange(0, spec_size::<T>() as int);
        self.write_raw(asid, spa, bytes)
    }

    pub open spec fn to_write(&self, i: SPA, asid: ASID, spmem: SPMem, bytes: Seq<Byte>) -> EncryptedByte
    {
        let crypto_mask: Byte = self.crypto_mask[self.spec_write_count()].get_mask();
        if spmem.contains(i)
        {
            let k = i.as_int() - spmem[0].as_int();
            SymKey{key: (asid, idx(i))}.encrypt(
                bytes[k],
                crypto_mask)
        } else if memrange_contains_block(spmem, idx(i))  {
            SymKey{key: (asid, idx(i))}.encrypt(
                SymKey{key: (asid, idx(i))}.decrypt(self.data[i.as_int()]),
                crypto_mask
            )
        } else {
            self.data[i.as_int()]
        }
    }

    pub open spec fn write_raw(&self, asid: ASID, spmem: SPMem, bytes: Seq<Byte>) -> Self
    {
        let mut new = *self;
        let bytes =
        Stream::new(
            self.spec_data().len(),
            |i: int|
            self.to_write(SPA::new(i), asid, spmem, bytes)
        );
        self.spec_set_data(bytes).spec_set_write_count(self.spec_write_count() + 1)
    }


    pub open spec fn read_one_byte(&self, asid: ASID, spa: SPA) -> Byte {
        SymKey{key: (asid, idx(spa))}.decrypt(self.data[spa.as_int()])
    }

    pub open spec fn read_byte_at(&self, asid: ASID, spmem: SPMem, i: int) -> Byte {
        if 0 <= i < spmem.len() {
            self.read_one_byte(asid, spmem[i])
        } else {
            0
        }
    }

    /// Only the VM itself can decrypt the data at the exact spa;
    #[verifier(inline)]
    pub open spec fn read_bytes_by_asid(&self, asid: ASID, spmem: SPMem) -> ByteStream {
        Stream::new(
            spmem.len(),
            |i: int| self.read_one_byte(asid, spmem[i])
        )
    }

    //#[verifier(opaque)]
    pub open spec fn read_by_asid<T: VTypeCast<Seq<u8>>>(&self, asid: ASID, spmem: SPMem) -> T {
        let bytes = self.read_bytes_by_asid(asid, spmem);
        stream_to_data(bytes)
    }

    pub open spec fn disjoint_write_read_requires(&self, asid: ASID, spa: SPMem, rspa: SPMem) -> bool
    {
        &&& rspa.disjoint(spa)
    }

    /// Only the VM itself can decrypt the data at the exact spa;
    #[verifier(opaque)]
    pub open spec fn read_all_by_asid(&self, asid: ASID) -> ByteStream {
        Stream::new(
            self.data.len(),
            |i: int| if !SPA::new(0).to_page().is_null() {
                    SymKey{key: (asid, idx2(i))}.decrypt(self.data[i])
                } else {
                    0
                }
        )
    }

    pub open spec fn hv_update(&self, newram: Self, memid: MemID) -> Self {
        newram
    }

    pub open spec fn hv_view(&self, memid: MemID) -> ByteStream {
        self.read_all_by_asid(memid.to_asid())
    }
}
}
