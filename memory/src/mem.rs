use std::collections::{HashMap, VecDeque};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicPtr, AtomicU8};
use std::sync::Mutex;
use std::{alloc::Layout, sync::atomic::Ordering};

use bytemuck::Pod;

#[derive(Clone, Default)]
pub struct Memory {
    internal: rclite::Arc<Internal>,
}

#[repr(C)]
#[derive(Default)]
struct Internal {
    pages: PageMap,
    page_handlers: Mutex<PageHandlers>,
}

#[derive(Default)]
struct PageHandlers{
    address_map: HashMap<usize, Box<dyn Page>>,
    available_pages: VecDeque<NonNull<PageContents>>,
}

impl Drop for Internal {
    fn drop(&mut self) {
        let PageHandlers{ address_map, available_pages } = self.page_handlers.get_mut().unwrap();
        for (page_id, ptr) in self.pages.pages.iter_mut().enumerate() {
            if *ptr.get_mut() == ALLOCATING_PAGE {
                panic!()
            } else if !ptr.get_mut().is_null() {
                let page = address_map.get_mut(&((*ptr.get_mut()) as usize)).unwrap();
                unsafe {
                    page.unpage(page_id as u32, *ptr.get_mut());
                    page.deinit(*ptr.get_mut());
                }
            }
        }

        for queued in available_pages {
            let page = address_map.get_mut(&(queued.as_ptr() as usize)).unwrap();
            unsafe {
                page.deinit(queued.as_ptr());
            }
        }
    }
}

impl Internal {
    unsafe fn map_page_unchecked<P: Page>(&self, page_id: u32, mut page: P) -> *const PageContents {
        let ptr = page.init();
        let mut lock = self.page_handlers.lock().unwrap();

        lock.address_map.insert(ptr as usize, Box::new(page));
        let item = lock.address_map.get_mut(&(ptr as usize)).unwrap();

        // we can assume that no one else tried to allocate because we swapped
        // the value for our marker value ALLOCATING_PAGE.
        self.pages
            .get_from_page_id(page_id)
            .store(ptr, Ordering::Release);
        item.page(page_id, ptr);
        ptr
    }

    unsafe fn unmap_page_unchecked(&self, page_id: u32, contents: *mut PageContents) {
        let mut lock = self.page_handlers.lock().unwrap();
        lock.address_map
            .get_mut(&(contents as usize))
            .unwrap()
            .unpage(page_id, contents);
        lock.available_pages
            .push_back(unsafe { NonNull::new_unchecked(contents) });
    }
}

/// # Safety
/// The type this is implemented on but have no uninitialized/unused/padding bytes.
///
/// All bit representations must be valid. (e.g. `NonZeroU32`, `char`)
///
/// Alignment must be equal to the size. (e.g. `[u32; 4]` doesn't meet this requirement but `u32` does)
/// 
/// The size of Self must not exeed `std::mem::size_of::<PageContents>()`
pub unsafe trait PermittedData: Pod {
    const TEST: () = test::<Self>();
}

const fn test<T>(){
    assert!(std::mem::size_of::<T>() <= std::mem::align_of::<T>());
    assert!(std::mem::size_of::<T>() <= std::mem::size_of::<PageContents>());
    assert!(std::mem::align_of::<T>() <= std::mem::align_of::<PageContents>());
}

#[test]
fn bruh(){
    testttt([0u8; 2])
}

unsafe impl PermittedData for [u8;2] {}

#[cfg(target_has_atomic = "8")]
unsafe impl PermittedData for u8 {}
#[cfg(target_has_atomic = "8")]
unsafe impl PermittedData for i8 {}

#[cfg(target_has_atomic = "16")]
unsafe impl PermittedData for u16 {}
#[cfg(target_has_atomic = "16")]
unsafe impl PermittedData for i16 {}

#[cfg(target_has_atomic = "32")]
unsafe impl PermittedData for u32 {}
#[cfg(target_has_atomic = "32")]
unsafe impl PermittedData for i32 {}
#[cfg(target_has_atomic = "32")]
unsafe impl PermittedData for f32 {}

#[cfg(target_has_atomic = "64")]
unsafe impl PermittedData for u64 {}
#[cfg(target_has_atomic = "64")]
unsafe impl PermittedData for i64 {}
#[cfg(target_has_atomic = "64")]
unsafe impl PermittedData for f64 {}

const PAGE_OFFSET_BITS: usize = 12;
const PAGE_MAP_BITS: usize = 32-PAGE_OFFSET_BITS;
const NUM_PAGES: usize = 1<<PAGE_MAP_BITS;
const PAGE_SIZE: usize = 1<<PAGE_OFFSET_BITS;

const EMPTY_PAGE: *mut PageContents = std::ptr::null_mut();
const ALLOCATING_PAGE: *mut PageContents = std::ptr::NonNull::dangling().as_ptr();

struct PageMap {
    pages: [AtomicPtr<PageContents>; NUM_PAGES],
}

impl Default for PageMap {
    fn default() -> Self {
        // this is just used to fill the array
        #[allow(clippy::declare_interior_mutable_const)]
        const EMPTY_PAGE_ATOMIC: AtomicPtr<PageContents> = AtomicPtr::new(EMPTY_PAGE);
        Self {
            pages: [EMPTY_PAGE_ATOMIC; NUM_PAGES],
        }
    }
}

impl PageMap {
    #[inline(always)]
    fn load_from_addr(&self, addr: u32) -> *mut PageContents {
        self.load_from_page(addr >> PAGE_OFFSET_BITS)
    }

    #[inline(always)]
    fn load_from_page(&self, page_id: u32) -> *mut PageContents {
        self.pages[page_id as usize].load(Ordering::Acquire)
    }

    #[inline(always)]
    const fn get_from_page_id(&self, page_id: u32) -> &AtomicPtr<PageContents> {
        &self.pages[page_id as usize]
    }
}

/// # Safety
/// 
/// 
pub unsafe trait Page: 'static {
    /// # Safety
    /// 
    unsafe fn init(&mut self) -> *mut PageContents;
    
    /// # Safety
    /// 
    unsafe fn page(&mut self, page_id: u32, page: *mut PageContents);    
    
    /// # Safety
    /// 
    unsafe fn unpage(&mut self, page_id: u32, page: *mut PageContents);    
    
    /// # Safety
    /// 
    unsafe fn deinit(&mut self, page: *mut PageContents);
}

struct FlatPage;
unsafe impl Page for FlatPage {
    unsafe fn init(&mut self) -> *mut PageContents {
        let ptr = unsafe { std::alloc::alloc(Layout::new::<PageContents>()) };
        if ptr.is_null() {
            std::alloc::handle_alloc_error(Layout::new::<PageContents>());
        }
        unsafe {
            ptr.write_bytes(0, std::mem::size_of::<PageContents>());
        }
        ptr.cast()
    }

    unsafe fn page(&mut self, _page_id: u32, _page: *mut PageContents) {}
    unsafe fn unpage(&mut self, _page_id: u32, _page: *mut PageContents) {}

    unsafe fn deinit(&mut self, page: *mut PageContents) {
        unsafe { std::alloc::dealloc(page.cast(), Layout::new::<PageContents>()) }
    }
}

#[repr(C, align(4096))]
pub struct PageContents {
    memory: [AtomicU8; PAGE_SIZE],
}

impl PageContents {
    /// # Safety
    /// 
    /// The pointer must not outlive self
    #[inline(always)]
    pub unsafe fn as_ptr(&self) -> *const [AtomicU8; PAGE_SIZE] {
        &self.memory
    }

    #[inline(always)]
    pub fn get<T: PermittedData>(&self, addr: u32) -> &atomic::Atomic<T> {
        unsafe { &*self.get_ptr(addr) }
    }

    /// # Safety
    /// 
    /// The pointer must not outlive self
    #[inline(always)]
    pub unsafe fn get_ptr<T: PermittedData>(&self, addr: u32) -> *const atomic::Atomic<T> {
        unsafe {
            self.memory
                .as_ptr()
                .byte_add(calculate_page_offset::<T>(addr))
                .cast::<atomic::Atomic<T>>()
        }
    }
}

#[inline(always)]
const fn page_offset_mask<T>() -> u32 {
    (PAGE_SIZE as u32 - 1) - (std::mem::align_of::<T>() - 1) as u32
}

#[inline(always)]
const fn calculate_page_offset<T>(addr: u32) -> usize {
    (addr & page_offset_mask::<T>()) as usize
}

mod arc_opts{
    #[cfg(target_pointer_width = "64")]
    pub(crate) use core::sync::atomic::AtomicU32 as AtomicCounter;
    
    #[cfg(all(
        not(target_pointer_width = "64"),
        not(target_pointer_width = "16"),
        not(target_pointer_width = "8"),
        feature = "usize-for-small-platforms",
    ))]
    pub(crate) use core::sync::atomic::AtomicUsize as AtomicCounter;
    
    #[cfg(all(
        target_pointer_width = "32",
        not(feature = "usize-for-small-platforms")
    ))]
    pub(crate) use core::sync::atomic::AtomicU16 as AtomicCounter;
    
    
    #[repr(C)]
    pub struct ArcInner<T> {
        pub data: std::cell::UnsafeCell<T>,
        pub counter: AtomicCounter,
    }
}


impl Memory {
    pub fn new() -> Self {
        let raw = unsafe{
            std::alloc::alloc(std::alloc::Layout::new::<arc_opts::ArcInner<Internal>>())
        };
        if raw.is_null(){
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<arc_opts::ArcInner<Internal>>());
        }
        let ptr: *mut arc_opts::ArcInner<Internal> = raw.cast();
        unsafe{
            let internal = std::ptr::addr_of_mut!((*ptr).data).cast::<Internal>();
            std::ptr::addr_of_mut!((*internal).page_handlers).write(Default::default());
            std::ptr::addr_of_mut!((*internal).pages).write_bytes(0, 1);
            std::ptr::addr_of_mut!((*ptr).counter).write(arc_opts::AtomicCounter::new(1));
        }
        Self {
            internal: unsafe{ rclite::Arc::from_raw(ptr.cast()) },
        }
    }

    pub fn ensure_page(&self, page_id: u32) {
        _ = self.try_map_page(page_id, FlatPage);
    }

    pub fn try_map_page<P: Page>(&self, page_id: u32, page: P) -> (*const PageContents, Result<(), P>) {
        let mut curr_page_contents = self
            .internal
            .pages
            .get_from_page_id(page_id)
            .swap(ALLOCATING_PAGE, Ordering::AcqRel);

        if curr_page_contents.is_null() {
            (
                unsafe { self.internal.map_page_unchecked(page_id, page) },
                Ok(()),
            )
        } else if curr_page_contents == ALLOCATING_PAGE {
            while curr_page_contents == ALLOCATING_PAGE {
                curr_page_contents = self.internal.pages.load_from_page(page_id);
                std::hint::spin_loop()
            }
            (curr_page_contents, Err(page))
        } else {
            self.internal
                .pages
                .get_from_page_id(page_id)
                .store(curr_page_contents, Ordering::Release);
            (curr_page_contents, Err(page))
        }
    }

    pub fn map_page<P: Page>(&self, page_id: u32, page: P) -> *const PageContents {
        let mut curr_page_contents = self
            .internal
            .pages
            .get_from_page_id(page_id)
            .swap(ALLOCATING_PAGE, Ordering::Acquire);

        if curr_page_contents.is_null() {
            unsafe { self.internal.map_page_unchecked(page_id, page) }
        } else if curr_page_contents == ALLOCATING_PAGE {
            while curr_page_contents == ALLOCATING_PAGE {
                curr_page_contents = self
                    .internal
                    .pages
                    .get_from_page_id(page_id)
                    .swap(ALLOCATING_PAGE, Ordering::AcqRel);
                std::hint::spin_loop()
            }
            if !curr_page_contents.is_null() {
                unsafe {
                    self.internal
                        .unmap_page_unchecked(page_id, curr_page_contents)
                }
            }
            unsafe { self.internal.map_page_unchecked(page_id, page) }
        } else {
            self.internal
                .pages
                .get_from_page_id(page_id)
                .store(curr_page_contents, Ordering::Release);

            unsafe {
                self.internal
                    .unmap_page_unchecked(page_id, curr_page_contents)
            }
            unsafe { self.internal.map_page_unchecked(page_id, page) }
        }
    }

    pub fn unmap_page(&self, page_id: u32) {
        let page_ptr = self.internal.pages.get_from_page_id(page_id);

        let mut current = page_ptr.load(Ordering::Acquire);
        while current == ALLOCATING_PAGE {
            current = page_ptr.load(Ordering::Acquire)
        }

        if !current.is_null() {
            unsafe { self.internal.unmap_page_unchecked(page_id, current) }
        }
    }

    #[cold]
    #[inline(never)]
    fn failure_get<T: PermittedData>(&self, addr: u32) -> NonNull<atomic::Atomic<T>> {
        let page = self.try_map_page(addr >> PAGE_OFFSET_BITS, FlatPage).0;
        unsafe { NonNull::new((*page).get_ptr(addr).cast_mut()).unwrap_unchecked() }
    }

    /// # Safety
    /// The returned pointer must not outlive this structure.
    ///
    /// The returned pointer will always be valid.
    ///
    /// The returned pointer should be used and discarded as quickely as possible. it is not
    /// Undefined behavior when kept around long enough but the mapping of the pointed to memory in this virtual memory
    /// Can change while holding onto the pointer. This can cause unintended side effects and behavior
    #[inline(always)]
    pub unsafe fn get<T: PermittedData>(&self, addr: u32) -> NonNull<atomic::Atomic<T>> {
        let page = self.internal.pages.load_from_addr(addr);
        if page > ALLOCATING_PAGE {
            unsafe { NonNull::new((*page).get_ptr(addr).cast_mut()).unwrap_unchecked() }
        } else {
            self.failure_get(addr)
        }
    }

    /// # Safety
    /// The returned pointer must not outlive this structure.
    ///
    /// The returned pointer will always be valid.
    ///
    /// The returned pointer should be used and discarded as quickely as possible. it is not
    /// Undefined behavior when kept around long enough but the mapping of the pointed to memory in this virtual memory
    /// Can change while holding onto the pointer. This can cause unintended side effects and behavior
    #[inline(always)]
    pub unsafe fn try_get<T: PermittedData>(
        &self,
        addr: u32,
    ) -> Option<NonNull<atomic::Atomic<T>>> {
        let page = self.internal.pages.load_from_addr(addr);
        if page > ALLOCATING_PAGE {
            NonNull::new(unsafe { (*page).get_ptr(addr).cast_mut() })
        } else {
            None
        }
    }

    #[cold]
    #[inline(never)]
    fn failure_load<T: PermittedData>(&self, addr: u32, ordering: Ordering) -> T {
        let page = self.try_map_page(addr >> PAGE_OFFSET_BITS, FlatPage).0;
        unsafe { (*page).get(addr).load(ordering) }
    }

    #[cold]
    #[inline(never)]
    fn failure_load_le<T: num_traits::PrimInt + PermittedData>(&self, addr: u32, ordering: Ordering) -> T {
        let page = self.try_map_page(addr >> PAGE_OFFSET_BITS, FlatPage).0;
        unsafe { (*page).get::<T>(addr).load(ordering).to_le() }
    }

    #[cold]
    #[inline(never)]
    fn failure_load_be<T: num_traits::PrimInt + PermittedData>(&self, addr: u32, ordering: Ordering) -> T {
        let page = self.try_map_page(addr >> PAGE_OFFSET_BITS, FlatPage).0;
        unsafe { (*page).get::<T>(addr).load(ordering).to_be() }
    }

    #[inline(always)]
    pub fn load<T: PermittedData>(&self, addr: u32, ordering: Ordering) -> T {
        assert!(std::mem::size_of::<T>() <= std::mem::align_of::<T>());
        assert!(std::mem::size_of::<T>() <= std::mem::size_of::<PageContents>());
        assert!(std::mem::align_of::<T>() <= std::mem::align_of::<PageContents>());


        let page = self.internal.pages.load_from_addr(addr);
        if page > ALLOCATING_PAGE {
            unsafe { (*page).get(addr).load(ordering) }
        } else {
            self.failure_load(addr, ordering)
        }
    }

    #[inline(always)]
    pub fn load_le<T: num_traits::PrimInt + PermittedData>(&self, addr: u32, ordering: Ordering) -> T {
        let page = self.internal.pages.load_from_addr(addr);
        if page > ALLOCATING_PAGE {
            unsafe { (*page).get::<T>(addr).load(ordering).to_le() }
        } else {
            self.failure_load_le(addr, ordering)
        }
    }

    #[inline(always)]
    pub fn load_be<T: num_traits::PrimInt + PermittedData>(&self, addr: u32, ordering: Ordering) -> T {
        let page = self.internal.pages.load_from_addr(addr);
        if page > ALLOCATING_PAGE {
            unsafe { (*page).get::<T>(addr).load(ordering).to_be() }
        } else {
            self.failure_load_be(addr, ordering)
        }
    }

    #[cold]
    #[inline(never)]
    fn failure_store<T: PermittedData>(&self, val: T, addr: u32, ordering: Ordering) {
        let page = self.try_map_page(addr >> PAGE_OFFSET_BITS, FlatPage).0;
        unsafe { (*page).get(addr).store(val, ordering) }
    }

    #[inline(always)]
    pub fn store<T: PermittedData>(&self, val: T, addr: u32, ordering: Ordering) {
        let page = self.internal.pages.load_from_addr(addr);

        if page > ALLOCATING_PAGE {
            unsafe { (*page).get(addr).store(val, ordering) }
        } else {
            self.failure_store(val, addr, ordering)
        }
    }

    #[inline(always)]
    pub fn store_be<T: num_traits::PrimInt + PermittedData>(&self, val: T, addr: u32, ordering: Ordering) {
        let page = self.internal.pages.load_from_addr(addr);

        if page > ALLOCATING_PAGE {
            unsafe { (*page).get(addr).store(val.to_be(), ordering) }
        } else {
            self.failure_store(val.to_be(), addr, ordering)
        }
    }

    #[inline(always)]
    pub fn store_le<T: num_traits::PrimInt + PermittedData>(&self, val: T, addr: u32, ordering: Ordering) {
        let page = self.internal.pages.load_from_addr(addr);

        if page > ALLOCATING_PAGE {
            unsafe { (*page).get(addr).store(val.to_le(), ordering) }
        } else {
            self.failure_store(val.to_le(), addr, ordering)
        }
    }

    #[inline(always)]
    pub fn try_load<T: PermittedData>(&self, addr: u32, ordering: Ordering) -> Option<T> {
        let page = self.internal.pages.load_from_addr(addr);
        if page > ALLOCATING_PAGE {
            Some(unsafe { (*page).get(addr).load(ordering) })
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn try_load_be<T: num_traits::PrimInt + PermittedData>(&self, addr: u32, ordering: Ordering) -> Option<T> {
        let page = self.internal.pages.load_from_addr(addr);
        if page > ALLOCATING_PAGE {
            Some(unsafe { (*page).get::<T>(addr).load(ordering).to_be() })
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn try_load_le<T: num_traits::PrimInt + PermittedData>(&self, addr: u32, ordering: Ordering) -> Option<T> {
        let page = self.internal.pages.load_from_addr(addr);
        if page > ALLOCATING_PAGE {
            Some(unsafe { (*page).get::<T>(addr).load(ordering).to_le() })
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn try_store<T: PermittedData>(
        &self,
        val: T,
        addr: u32,
        ordering: Ordering,
    ) -> Result<(), T> {
        let page = self.internal.pages.load_from_addr(addr);

        if page > ALLOCATING_PAGE {
            unsafe { (*page).get(addr).store(val, ordering) }
            Ok(())
        } else {
            Err(val)
        }
    }

    #[inline(always)]
    pub fn try_store_be<T: num_traits::PrimInt + PermittedData>(
        &self,
        val: T,
        addr: u32,
        ordering: Ordering,
    ) -> Result<(), T> {
        let page = self.internal.pages.load_from_addr(addr);

        if page > ALLOCATING_PAGE {
            unsafe { (*page).get(addr).store(val.to_be(), ordering) }
            Ok(())
        } else {
            Err(val)
        }
    }

    #[inline(always)]
    pub fn try_store_le<T: num_traits::PrimInt + PermittedData>(
        &self,
        val: T,
        addr: u32,
        ordering: Ordering,
    ) -> Result<(), T> {
        let page = self.internal.pages.load_from_addr(addr);

        if page > ALLOCATING_PAGE {
            unsafe { (*page).get(addr).store(val.to_le(), ordering) }
            Ok(())
        } else {
            Err(val)
        }
    }
}

#[inline(never)]
pub fn test_get(mem: &Memory, addr: u32) -> u16 {
    mem.load(addr, Ordering::SeqCst)
}

pub fn test_set(mem: &Memory, val: u32, addr: u32) {
    mem.store_be(val, addr, Ordering::SeqCst);
}


#[test]
pub fn allocate_all(){
    let mem = Memory::new();

    for i in (0..=u32::MAX).step_by(PAGE_SIZE) {
        mem.store(0xFFu8, i, Ordering::Relaxed);
    }

    let now = std::time::Instant::now();
    for i in (0..=u32::MAX).step_by(4) {
        mem.store(i, i, Ordering::Relaxed);
    }
    println!("write: {:.2}s", now.elapsed().as_secs_f32());
    let now = std::time::Instant::now();
    for i in (0..=u32::MAX).step_by(4) {
        assert_eq!(mem.load::<u32>(i, Ordering::Relaxed), i);
    }
    println!("check: {:.2}s", now.elapsed().as_secs_f32());

    


    //
    let now = std::time::Instant::now();
    for i in (0..=1<<25).step_by(4) {
        mem.store(i, i, Ordering::Relaxed);
    }
    println!("write: {:.2}s", now.elapsed().as_secs_f32());
    let now = std::time::Instant::now();
    for i in (0..=1<<25).step_by(4) {
        assert_eq!(mem.load::<u32>(i, Ordering::Relaxed), i);
    }
    println!("check: {:.2}s", now.elapsed().as_secs_f32());
}

#[test]
pub fn shared_memory() {


    #[derive(Clone)]
    struct SharedPage(rclite::Arc<*mut PageContents>);
    impl SharedPage {
        pub fn new() -> Self {
            Self(rclite::Arc::new(unsafe { FlatPage::init(&mut FlatPage) }))
        }
    }
    unsafe impl Page for SharedPage {
        unsafe fn init(&mut self) -> *mut PageContents {
            *self.0
        }
        unsafe fn page(&mut self, _: u32, _: *mut PageContents) {}
        unsafe fn unpage(&mut self, _: u32, _: *mut PageContents) {}
        unsafe fn deinit(&mut self, _page: *mut PageContents) {}
    }
    impl Drop for SharedPage {
        fn drop(&mut self) {
            if let Some(_) = rclite::Arc::get_mut(&mut self.0){
                unsafe { FlatPage::deinit(&mut FlatPage, *self.0) }
            }
        }
    }

    let mem = Memory::new();
    let shared = SharedPage::new();
    mem.map_page(0, shared.clone());
    mem.map_page(1, shared);

    for i in [0, 1, 1<<15, 1<<16-2, 1<<16-1] {
        println!("s{i}");
        _ = mem.store::<u16>(i as u16, i as u32, Ordering::Relaxed);
    }

    for i in [0, 1, 1<<15, 1<<16-2, 1<<16-1] {
        println!("l{i}");
        assert_eq!(
            mem.load::<u16>(i as u32, Ordering::Relaxed),
            mem.load::<u16>(i as u32 + PAGE_SIZE as u32, Ordering::Relaxed)
        )
    }
}

#[test]
pub fn externally_updating() {
    use std::sync::atomic::AtomicU32;

    struct Nice{
        val: AtomicU32,
        other: AtomicU8,
    }

    #[derive(Clone)]
    struct SharedPage(rclite::Arc<*mut PageContents>);
    impl SharedPage {
        pub fn new() -> Self {
            Self(rclite::Arc::new(unsafe { FlatPage::init(&mut FlatPage) }))
        }

        pub fn get(&self) -> &Nice{
            unsafe{ &*self.0.cast() }
        }
    }
    unsafe impl Page for SharedPage {
        unsafe fn init(&mut self) -> *mut PageContents {
            *self.0
        }
        unsafe fn page(&mut self, _: u32, _: *mut PageContents) {}
        unsafe fn unpage(&mut self, _: u32, _: *mut PageContents) {}
        unsafe fn deinit(&mut self, _: *mut PageContents) {}
    }
    impl Drop for SharedPage {
        fn drop(&mut self) {
            if let Some(_) = rclite::Arc::get_mut(&mut self.0){
                unsafe { FlatPage::deinit(&mut FlatPage, *self.0) }
            }
        }
    }

    let mem = Memory::new();
    let shared = SharedPage::new();
    let nice = shared.get();
    mem.map_page(0, shared.clone());


    nice.val.store(558822, Ordering::Relaxed);
    nice.other.store(0xFF, Ordering::Relaxed);

    let val = mem.load::<u32>(0, Ordering::Relaxed);
    let other = mem.load::<u8>(4, Ordering::Relaxed);

    assert_eq!(val, 558822);
    assert_eq!(other, 0xFF);

    mem.store::<u32>(44, 0, Ordering::Relaxed);
    mem.store::<u8>(11, 4, Ordering::Relaxed);

    let val = nice.val.load(Ordering::Relaxed);
    let other = nice.other.load(Ordering::Relaxed);

    assert_eq!(val, 44);
    assert_eq!(other, 11);
}
