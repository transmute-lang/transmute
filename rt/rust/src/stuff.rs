////////////////////////////////////////////////////////////////////////////////////////////////////

use std::cell::{Cell, RefCell};
use std::marker::{PhantomData, PhantomPinned};

/// Helper trait to break the dependency between an object and the lifetimes of
/// it's [traceable](Trace) children. If This trait is implemented, then the
/// object can be traced by the garbage collector. Once it becomes rooted, it as
/// well as all of it's tracable children will be live until it is unrooted.
/// This essentially makes any lifetimes of a tracable objects meaningless. They
/// can be anything, including 'static. When an object is removed from a root it
/// will be given the proper lifetime again. Care must be taken to ensure that
/// any lifetimes that are changed only belong to traceable objects. Object can
/// contain lifetimes parameters for both traceable and untracable children, and
/// only the traceable children's lifetimes can be changed.
///
/// On top of scrubbing the lifetimes, this trait can also do a transformation
/// of the underlying type for convenience, similar to calling `Into::into`.
#[diagnostic::on_unimplemented(
    message = "`{Self}` does not implement `Trace`",
    label = "cannot be rooted",
    note = "Use #[derive(Trace)] to make `{Self}` Rootable",
    note = "If this is a foreign type, implement `Trace` and `IntoRoot` manually"
)]
trait IntoRoot<T> {
    unsafe fn into_root(self) -> T;
}

impl<T, U> IntoRoot<Vec<U>> for Vec<T>
    where
        T: IntoRoot<U>,
{
    unsafe fn into_root(self) -> Vec<U> {
        let mut new = Vec::with_capacity(self.len());
        for x in self {
            new.push(x.into_root());
        }
        new
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[macro_export]
macro_rules! __root {
    ($ident:ident, $cx:ident) => {
        rune_core::macros::root!(@ $ident, unsafe { IntoRoot::into_root($ident) }, $cx);
    };
    // ($ident:ident, init($init:expr), $cx:ident) => {
    //     let value = $init;
    //     rune_core::macros::root!(@ $ident, value, $cx);
    // };
    // ($ident:ident, new($path:tt$(<$ty:ty>)?), $cx:ident) => {
    //     let value = $path$(::<$ty>)?::default();
    //     rune_core::macros::root!(@ $ident, value, $cx);
    // };
    // ($ident:ident, $value:expr, $cx:ident) => {
    //     rune_core::macros::root!(@ $ident, unsafe { crate::core::gc::IntoRoot::into_root($value) }, $cx);
    // };
    (@ $ident:ident, $value:expr, $cx:ident) => {
        let mut rooted = $value;
        let mut root =
            unsafe { crate::core::gc::__StackRoot::new(&mut rooted, $cx.get_root_set()) };
        let $ident = root.as_mut();
    };
}

////////////////////////////////////////////////////////////////////////////////////////////////////

// Represents an object T rooted on the Stack. This will remove the the object
// from the root set when dropped.
struct __StackRoot<'rt, T> {
    data: &'rt mut Rt<T>,
    root_set: &'rt RootSet,
}

// Do not use this function directly. Use the `root` macro instead.
//
// SAFETY: An owned StackRoot must never be exposed to the rest of the program.
// That could result in calling `mem::forget` on the root, which would
// invalidate the stack property of the root set.
impl<'rt, T: Trace> __StackRoot<'rt, T> {
    unsafe fn new(data: &'rt mut T, root_set: &'rt RootSet) -> __StackRoot<'rt, T> {
        let dyn_ptr = data as &mut dyn Trace as *mut dyn Trace;
        // We are using this transmute to dissociate the `dyn Trace` from the T.
        // Otherwise rust tries to require us to add a 'static bound. We don't
        // need this because stackroot can't outlive data (due to the 'rt
        // lifetime), and therefore it can't outlive T.
        let dyn_ptr = std::mem::transmute::<*mut dyn Trace, *mut dyn Trace>(dyn_ptr);
        let data = &mut *(dyn_ptr.cast::<Rt<T>>());
        let root = Self { data, root_set };
        root_set.roots.borrow_mut().push(dyn_ptr);
        root
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// A "Root Tracable" type. If a type is wrapped in Rt, it is known to be rooted
/// and hold items past garbage collection. This type is never used as an owned
/// type, only a reference. This ensures that underlying data does not move. In
/// order to access the inner data, use [`Rt::bind_ref`] or [`Rt::bind_mut`]
/// methods.
#[derive(PartialEq, Eq)]
struct Rt<T: ?Sized> {
    _aliasable: PhantomPinned,
    inner: T,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// Owns all allocations and creates objects. All objects have
/// a lifetime tied to the borrow of their `Context`. When the
/// `Context` goes out of scope, no objects should be accessible.
pub struct Context<'rt> {
    root_set: &'rt RootSet,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// A global store of all gc roots. This struct should be passed to the [Context]
/// when it is created.
#[derive(Default, Debug)]
pub struct RootSet {
    roots: RefCell<Vec<*const dyn Trace>>,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

struct GcState {
    stack: Vec<RawObj>,
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// A raw pointer to a GC heap managed object
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct RawObj {
    ptr: *const u8,
}
unsafe impl Send for RawObj {}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// This type is something that is managed by the GC. It is intended to be pointer sized, and
/// have a lifetime tied to the context which manages garbage collections.
#[derive(Copy, Clone)]
struct Gc<T> {
    ptr: *const u8,
    _data: PhantomData<T>,
}

unsafe impl<T> Send for Gc<T> where T: Send {}

impl<T> Gc<T> {
    const fn new(ptr: *const u8) -> Self {
        Self {
            ptr,
            _data: PhantomData,
        }
    }

    fn into_raw(self) -> RawObj {
        RawObj { ptr: self.ptr }
    }

    fn into_ptr(self) -> *const u8 {
        self.ptr
    }

    unsafe fn from_raw(raw: RawObj) -> Self {
        Self::new(raw.ptr)
    }

    unsafe fn from_raw_ptr(raw: *mut u8) -> Self {
        Self::new(raw)
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

/// A block of memory allocated on the heap that is managed by the garbage collector.
struct GcHeap<T: ?Sized> {
    marked: Cell<bool>,
    data: T,
}

unsafe impl<T: Sync> Sync for GcHeap<T> where T: Sync {}

impl<T> GcHeap<T> {
    const fn new(data: T) -> Self {
        Self {
            marked: Cell::new(false),
            data,
        }
    }

    fn is_marked(&self) -> bool {
        self.marked.get()
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

trait Trace {
    fn trace(&self);
}

impl<T> Trace for GcHeap<T>
    where
        T: Trace,
{
    fn trace(&self) {
        self.marked.replace(true);
        self.data.trace()
    }
}

impl<T> Trace for &T
    where
        T: Trace,
{
    fn trace(&self) {
        (*self).trace()
    }
}

impl<T> Trace for Vec<T>
    where
        T: Trace,
{
    fn trace(&self) {
        for x in self {
            x.trace();
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test() {}
}
