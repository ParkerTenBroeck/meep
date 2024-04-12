pub use bytemuck::Pod;
pub use bytemuck::Zeroable;

use crate::mem::PageContents;

trait IsTrue<const COND: bool> {}
impl IsTrue<true> for () {}

/// # Safety
///
/// The size of this type should be less than or equal to the alignment of it.
///
/// The size of this type should be less than or equal to the size of [`PageContents`]
///
/// The alignment of this type should be less than or equal to the alignment of [`PageContents`]
///
/// The type must also be plain data. where no invalid bit representation exists.
/// This also means it can be zeroed. See [`Pod`] for additional constraints
pub unsafe trait TriviallyLoadableData:
    Pod + SizeLessThanEqualAlign + SizeLessThanEqualPageSize + AlignLessThanEqualPageAlign
{
}

unsafe impl<T: Pod + SizeLessThanEqualAlign + SizeLessThanEqualPageSize + AlignLessThanEqualPageAlign>
    TriviallyLoadableData for T
{
}

pub unsafe trait SizeLessThanEqualAlign {}
unsafe impl<T> SizeLessThanEqualAlign for T where
    (): IsTrue<{ std::mem::size_of::<T>() <= std::mem::align_of::<T>() }>
{
}

pub unsafe trait SizeLessThanEqualPageSize {}
unsafe impl<T> SizeLessThanEqualPageSize for T where
    (): IsTrue<{ std::mem::size_of::<T>() <= std::mem::size_of::<PageContents>() }>
{
}

pub unsafe trait AlignLessThanEqualPageAlign {}
unsafe impl<T> AlignLessThanEqualPageAlign for T where
    (): IsTrue<{ std::mem::align_of::<T>() <= std::mem::align_of::<PageContents>() }>
{
}

pub const fn assert_permitted_data_preconditions<T: Pod>() {
    assert!(std::mem::size_of::<T>() <= std::mem::align_of::<T>());
    assert!(std::mem::size_of::<T>() <= std::mem::size_of::<PageContents>());
    assert!(std::mem::align_of::<T>() <= std::mem::align_of::<PageContents>());
}

pub const fn assert_lock_free_atomic_preconditions<T: Pod>() {
    assert!(atomic::Atomic::<T>::is_lock_free());
}

/// # Safety
///
/// The type this is implemented on should have platform and architecture level support for atomics
/// on this types size.
pub unsafe trait LockFreeAtomic {}
unsafe impl<T: TriviallyLoadableData> LockFreeAtomic for T where
    (): IsTrue<{ atomic::Atomic::<T>::is_lock_free() }>
{
}

// unsafe impl PermittedData for [u8;2] {}

// #[cfg(target_has_atomic = "8")]
// unsafe impl PermittedData for u8 {}
// #[cfg(target_has_atomic = "8")]
// unsafe impl PermittedData for i8 {}

// #[cfg(target_has_atomic = "16")]
// unsafe impl PermittedData for u16 {}
// #[cfg(target_has_atomic = "16")]
// unsafe impl PermittedData for i16 {}

// #[cfg(target_has_atomic = "32")]
// unsafe impl PermittedData for u32 {}
// #[cfg(target_has_atomic = "32")]
// unsafe impl PermittedData for i32 {}
// #[cfg(target_has_atomic = "32")]
// unsafe impl PermittedData for f32 {}

// #[cfg(target_has_atomic = "64")]
// unsafe impl PermittedData for u64 {}
// #[cfg(target_has_atomic = "64")]
// unsafe impl PermittedData for i64 {}
// #[cfg(target_has_atomic = "64")]
// unsafe impl PermittedData for f64 {}
