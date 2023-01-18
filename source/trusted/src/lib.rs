#![no_std]

mod trusted {
    use core::alloc::Layout;

    #[global_allocator]
    static ALLOCATOR: MyAllocator = MyAllocator;

    struct MyAllocator;
    unsafe impl core::alloc::GlobalAlloc for MyAllocator {
        unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
            unreachable!();
        }

        unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
            unreachable!();
        }
    }
}
