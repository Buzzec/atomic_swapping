//! A concurrent data structure that allows for [`AtomicSwap::swap`], [`AtomicSwap::take`], [`AtomicSwap::set`], and [`AtomicSwap::clone_inner`] operations to be run on any type `T`.
//! ```
//! use atomic_swap::AtomicSwap;
//!
//! let swap = AtomicSwap::new(Some(100usize));
//! assert_eq!(swap.clone_inner(), Some(100usize));
//! assert_eq!(swap.take(), Some(100usize));
//! assert_eq!(swap.take(), None);
//! swap.set(Some(200usize));
//! assert_eq!(swap.swap(Some(300usize)), Some(200usize));
//! assert!(swap.contains_value());
//! assert_eq!(swap.clone_inner(), Some(300usize));
//! ```
//! This is guaranteed lock-free where atomics will be guaranteed lock-free, however it is not guaranteed wait free. Some operations may spin for a short time.
//! All values will be properly dropped.

#![warn(missing_debug_implementations, missing_docs, unused_import_braces)]
#![cfg_attr(not(test), no_std)]

use core::cell::UnsafeCell;
use core::hint::spin_loop;
#[cfg(not(debug_assertions))]
use core::hint::unreachable_unchecked;
use core::mem::{swap, MaybeUninit};
use core::sync::atomic::{AtomicUsize, Ordering};

/// Allows shared access to `T` by only swap related operations. Acts like it stores an [`Option<T>`]
/// ```
/// use atomic_swap::AtomicSwap;
///
/// let swap = AtomicSwap::new(Some(100usize));
/// assert_eq!(swap.clone_inner(), Some(100usize));
/// assert_eq!(swap.take(), Some(100usize));
/// assert_eq!(swap.take(), None);
/// swap.set(Some(200usize));
/// assert_eq!(swap.swap(Some(300usize)), Some(200usize));
/// assert!(swap.contains_value());
/// assert_eq!(swap.clone_inner(), Some(300usize));
/// ```
#[derive(Debug)]
pub struct AtomicSwap<T> {
    state: AtomicUsize,
    data: UnsafeCell<MaybeUninit<T>>,
}
impl<T> AtomicSwap<T> {
    /// Creates a new [`AtomicSwap`] from an optional value.
    /// If `const` is needed then look to [`AtomicSwap::from_value`] or [`AtomicSwap::from_none`].
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let some_swap = AtomicSwap::new(Some(100usize));
    /// assert_eq!(some_swap.take(), Some(100usize));
    ///
    /// let none_swap = AtomicSwap::<usize>::new(None);
    /// assert_eq!(none_swap.take(), None);
    /// ```
    pub fn new(value: Option<T>) -> Self {
        match value {
            None => Self::from_none(),
            Some(value) => Self::from_value(value),
        }
    }
    /// Creates a new [`AtomicSwap`] from a value, assigning [`Some`] to the swap.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::from_value(100usize);
    /// assert_eq!(swap.take(), Some(100usize));
    /// ```
    pub const fn from_value(value: T) -> Self {
        Self {
            state: AtomicUsize::new(AtomicSwapState::Assigned(0).into_usize()),
            data: UnsafeCell::new(MaybeUninit::new(value)),
        }
    }
    /// Creates a new [`AtomicSwap`] with [`None`] assigned.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::<usize>::from_none();
    /// assert_eq!(swap.take(), None);
    /// ```
    pub const fn from_none() -> Self {
        Self {
            state: AtomicUsize::new(AtomicSwapState::Unassigned.into_usize()),
            data: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Swaps the current value in the swap with `value`, returning the currently contained value.
    /// Same as [`AtomicSwap::swap_hint`] with [`spin_loop`] as `spin_loop_hint`.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::from_value(100usize);
    /// assert_eq!(swap.swap(Some(200usize)), Some(100usize));
    /// assert_eq!(swap.swap(None), Some(200usize));
    /// assert_eq!(swap.swap(None), None);
    /// ```
    #[inline]
    pub fn swap(&self, value: Option<T>) -> Option<T> {
        self.swap_hint(value, spin_loop)
    }
    /// Swaps the current value in the swap with `value`, returning the currently contained value.
    /// Same as [`AtomicSwap::swap`] but with a custom spin loop hint function.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::from_value(100usize);
    /// let spin_hint = ||println!("I'm spinning! Probably should yield here.");
    /// assert_eq!(swap.swap_hint(Some(200usize), spin_hint), Some(100usize));
    /// assert_eq!(swap.swap_hint(None, spin_hint), Some(200usize));
    /// assert_eq!(swap.swap_hint(None, spin_hint), None);
    /// ```
    pub fn swap_hint(&self, value: Option<T>, mut spin_loop_hint: impl FnMut()) -> Option<T> {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            let state_enum = AtomicSwapState::from_usize(state);
            match &state_enum {
                AtomicSwapState::Unassigned | AtomicSwapState::Assigned(0) => {
                    match self.state.compare_exchange_weak(
                        state,
                        AtomicSwapState::Assigning.into_usize(),
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            let value_is_some = value.is_some();
                            let out = match (value, state_enum) {
                                (None, AtomicSwapState::Unassigned) => None,
                                (None, AtomicSwapState::Assigned(_)) => unsafe {
                                    Some(self.data.get().read().assume_init())
                                },
                                (Some(value), AtomicSwapState::Unassigned) => unsafe {
                                    *self.data.get() = MaybeUninit::new(value);
                                    None
                                },
                                (Some(value), AtomicSwapState::Assigned(_)) => unsafe {
                                    let mut out = MaybeUninit::new(value);
                                    swap(&mut out, &mut *self.data.get());
                                    Some(out.assume_init())
                                },
                                (_, _) => {
                                    #[cfg(debug_assertions)]
                                    unreachable!();
                                    #[cfg(not(debug_assertions))]
                                    unsafe {
                                        unreachable_unchecked()
                                    }
                                }
                            };
                            self.state
                                .compare_exchange(
                                    AtomicSwapState::Assigning.into_usize(),
                                    if value_is_some {
                                        AtomicSwapState::Assigned(0).into_usize()
                                    } else {
                                        AtomicSwapState::Unassigned.into_usize()
                                    },
                                    Ordering::AcqRel,
                                    Ordering::Acquire,
                                )
                                .expect("Assigning was changed improperly!");
                            return out;
                        }
                        Err(new_state) => state = new_state,
                    }
                }
                AtomicSwapState::Assigned(_) | AtomicSwapState::Assigning => {
                    spin_loop_hint();
                    state = self.state.load(Ordering::Acquire);
                }
            }
        }
    }

    /// Takes the current value and returns it leaving [`None`] in its place.
    /// Same as [`AtomicSwap::take_hint`] with [`spin_loop`] as `spin_loop_hint`.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::from_value(100usize);
    /// assert_eq!(swap.take(), Some(100usize));
    /// assert_eq!(swap.take(), None);
    /// ```
    #[inline]
    pub fn take(&self) -> Option<T> {
        self.take_hint(spin_loop)
    }
    /// Takes the current value and returns it leaving [`None`] in its place.
    /// Same as [`AtomicSwap::take`] but with a custom spin loop hint function.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::from_value(100usize);
    /// let spin_hint = ||println!("I'm spinning! Probably should yield here.");
    /// assert_eq!(swap.take_hint(spin_hint), Some(100usize));
    /// assert_eq!(swap.take_hint(spin_hint), None);
    /// ```
    pub fn take_hint(&self, mut spin_loop_hint: impl FnMut()) -> Option<T> {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            match AtomicSwapState::from_usize(state) {
                AtomicSwapState::Unassigned => return None,
                AtomicSwapState::Assigned(0) => match self.state.compare_exchange_weak(
                    state,
                    AtomicSwapState::Assigning.into_usize(),
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => unsafe {
                        let out = self.data.get().read().assume_init();
                        self.state
                            .compare_exchange(
                                AtomicSwapState::Assigning.into_usize(),
                                AtomicSwapState::Unassigned.into_usize(),
                                Ordering::AcqRel,
                                Ordering::Acquire,
                            )
                            .expect("Assigning was changed improperly!");
                        return Some(out);
                    },
                    Err(new_state) => state = new_state,
                },
                AtomicSwapState::Assigned(_) | AtomicSwapState::Assigning => {
                    spin_loop_hint();
                    state = self.state.load(Ordering::Acquire);
                }
            }
        }
    }

    /// Sets the current value in the swap to `value`, dropping the held value if contained.
    /// Same as [`AtomicSwap::set_hint`] with [`spin_loop`] as `spin_loop_hint`.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// # use std::sync::atomic::{AtomicUsize, Ordering};
    /// # use std::sync::Arc;
    /// # struct DropCount<T>(Arc<AtomicUsize>, T);
    /// # impl<T> Drop for DropCount<T>{
    /// #     fn drop(&mut self) {
    /// #         self.0.fetch_add(1, Ordering::SeqCst);
    /// #     }
    /// # }
    /// // drop_count is incremented every time a DropCount is dropped
    /// let drop_count = Arc::new(AtomicUsize::new(0));
    /// let swap = AtomicSwap::from_value(DropCount(drop_count.clone(), 100usize));
    ///
    /// // Setting the swap to None should drop 100
    /// swap.set(None);
    /// assert_eq!(1, drop_count.load(Ordering::SeqCst));
    /// // Setting the swap to 200 should drop nothing as contains None
    /// swap.set(Some(DropCount(drop_count.clone(), 200usize)));
    /// assert_eq!(1, drop_count.load(Ordering::SeqCst));
    /// // Setting the swap to 300 should drop 200
    /// swap.set(Some(DropCount(drop_count.clone(), 300usize)));
    /// assert_eq!(2, drop_count.load(Ordering::SeqCst));
    /// // Dropping the swap should drop 300
    /// drop(swap);
    /// assert_eq!(3, drop_count.load(Ordering::SeqCst));
    /// ```
    #[inline]
    pub fn set(&self, value: Option<T>) {
        self.set_hint(value, spin_loop)
    }
    /// Sets the current value in the swap to `value`, dropping the held value if contained.
    /// Same as [`AtomicSwap::set`] but with a custom spin loop hint function.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// # use std::sync::atomic::{AtomicUsize, Ordering};
    /// # use std::sync::Arc;
    /// # struct DropCount<T>(Arc<AtomicUsize>, T);
    /// # impl<T> Drop for DropCount<T>{
    /// #     fn drop(&mut self) {
    /// #         self.0.fetch_add(1, Ordering::SeqCst);
    /// #     }
    /// # }
    /// // drop_count is incremented every time a DropCount is dropped
    /// let drop_count = Arc::new(AtomicUsize::new(0));
    /// let swap = AtomicSwap::from_value(DropCount(drop_count.clone(), 100usize));
    /// let spin_hint = ||println!("I'm spinning! Probably should yield here.");
    ///
    /// // Setting the swap to None should drop 100
    /// swap.set_hint(None, spin_hint);
    /// assert_eq!(1, drop_count.load(Ordering::SeqCst));
    /// // Setting the swap to 200 should drop nothing as contains None
    /// swap.set_hint(Some(DropCount(drop_count.clone(), 200usize)), spin_hint);
    /// assert_eq!(1, drop_count.load(Ordering::SeqCst));
    /// // Setting the swap to 300 should drop 200
    /// swap.set_hint(Some(DropCount(drop_count.clone(), 300usize)), spin_hint);
    /// assert_eq!(2, drop_count.load(Ordering::SeqCst));
    /// // Dropping the swap should drop 300
    /// drop(swap);
    /// assert_eq!(3, drop_count.load(Ordering::SeqCst));
    /// ```
    pub fn set_hint(&self, value: Option<T>, mut spin_loop_hint: impl FnMut()) {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            let state_enum = AtomicSwapState::from_usize(state);
            match &state_enum {
                AtomicSwapState::Unassigned | AtomicSwapState::Assigned(0) => {
                    match self.state.compare_exchange_weak(
                        state,
                        AtomicSwapState::Assigning.into_usize(),
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            if let AtomicSwapState::Assigned(_) = state_enum {
                                unsafe { drop(self.data.get().read().assume_init()) }
                            }
                            let value_is_some = value.is_some();
                            if let Some(value) = value {
                                unsafe {
                                    *self.data.get() = MaybeUninit::new(value);
                                }
                            }
                            self.state
                                .compare_exchange(
                                    AtomicSwapState::Assigning.into_usize(),
                                    if value_is_some {
                                        AtomicSwapState::Assigned(0).into_usize()
                                    } else {
                                        AtomicSwapState::Unassigned.into_usize()
                                    },
                                    Ordering::AcqRel,
                                    Ordering::Acquire,
                                )
                                .expect("Assigning was changed improperly!");
                            return;
                        }
                        Err(new_state) => state = new_state,
                    }
                }
                AtomicSwapState::Assigned(_) | AtomicSwapState::Assigning => {
                    spin_loop_hint();
                    state = self.state.load(Ordering::Acquire);
                }
            }
        }
    }

    /// Clones the contained value if [`Some`] and returns it. `T` must be [`Clone`] and [`Sync`] because multiple threads could clone this simultaneously.
    /// Same as [`AtomicSwap::clone_inner_hint`] with [`spin_loop`] as `spin_loop_hint`.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::from_value(100usize);
    /// assert_eq!(swap.clone_inner(), Some(100usize));
    /// assert_eq!(swap.take(), Some(100usize));
    /// assert_eq!(swap.clone_inner(), None);
    /// assert_eq!(swap.take(), None);
    /// ```
    #[inline]
    pub fn clone_inner(&self) -> Option<T>
    where
        T: Clone + Sync,
    {
        self.clone_inner_hint(spin_loop)
    }
    /// Clones the contained value if [`Some`] and returns it. `T` must be [`Clone`] and [`Sync`] because multiple threads could clone this simultaneously.
    /// Same as [`AtomicSwap::clone_inner`] but with a custom spin loop hint function.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::from_value(100usize);
    /// let spin_hint = ||println!("I'm spinning! Probably should yield here.");
    /// assert_eq!(swap.clone_inner_hint(spin_hint), Some(100usize));
    /// assert_eq!(swap.take_hint(spin_hint), Some(100usize));
    /// assert_eq!(swap.clone_inner_hint(spin_hint), None);
    /// assert_eq!(swap.take_hint(spin_hint), None);
    /// ```
    pub fn clone_inner_hint(&self, mut spin_loop_hint: impl FnMut()) -> Option<T>
    where
        T: Clone + Sync,
    {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            match AtomicSwapState::from_usize(state) {
                AtomicSwapState::Unassigned => return None,
                AtomicSwapState::Assigned(readers) => match self.state.compare_exchange_weak(
                    state,
                    AtomicSwapState::Assigned(readers + 1).into_usize(),
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => unsafe {
                        // safe because MaybeUninit<T> is transparent to T while init
                        let out = (&*(self.data.get() as *mut T)).clone();
                        let result = self.state.fetch_sub(1, Ordering::AcqRel);
                        debug_assert_ne!(result, 0);
                        return Some(out);
                    },
                    Err(new_state) => state = new_state,
                },
                AtomicSwapState::Assigning => {
                    spin_loop_hint();
                    state = self.state.load(Ordering::Acquire);
                }
            }
        }
    }

    /// Returns true if the swap contains a value. Will return `true` if [`Some`], `false` if [`None`], or will spin if being assigned by other thread.
    /// Same as [`AtomicSwap::contains_value_hint`] with [`spin_loop`] as `spin_loop_hint`.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::from_value(100usize);
    /// assert!(swap.contains_value());
    /// assert_eq!(swap.take(), Some(100usize));
    /// assert!(!swap.contains_value());
    /// assert_eq!(swap.take(), None);
    /// ```
    #[inline]
    pub fn contains_value(&self) -> bool {
        self.contains_value_hint(spin_loop)
    }
    /// Returns true if the swap contains a value. Will return `true` if [`Some`], `false` if [`None`], or will spin if being assigned by other thread.
    /// Same as [`AtomicSwap::contains_value`] but with a custom spin loop hint function.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let swap = AtomicSwap::from_value(100usize);
    /// let spin_hint = ||println!("I'm spinning! Probably should yield here.");
    /// assert!(swap.contains_value_hint(spin_hint));
    /// assert_eq!(swap.take_hint(spin_hint), Some(100usize));
    /// assert!(!swap.contains_value_hint(spin_hint));
    /// assert_eq!(swap.take_hint(spin_hint), None);
    /// ```
    pub fn contains_value_hint(&self, mut spin_loop_hint: impl FnMut()) -> bool {
        loop {
            match AtomicSwapState::from_usize(self.state.load(Ordering::Acquire)) {
                AtomicSwapState::Unassigned => return false,
                AtomicSwapState::Assigning => spin_loop_hint(),
                AtomicSwapState::Assigned(_) => return true,
            }
        }
    }

    /// Gets the internal value exclusively if contains a value. Use [`AtomicSwap::get_mut_or`], [`AtomicSwap::get_mut_or_else`], or [`AtomicSwap::get_mut_default`] if wanting to guarantee a value is held.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let mut swap = AtomicSwap::from_value(100);
    /// assert_eq!(swap.get_mut(), Some(&mut 100usize));
    /// *swap.get_mut().unwrap() = 200usize;
    /// assert_eq!(swap.take(), Some(200usize));
    /// assert_eq!(swap.get_mut(), None);
    /// ```
    pub fn get_mut(&mut self) -> Option<&mut T> {
        match AtomicSwapState::from_usize(self.state.load(Ordering::Acquire)) {
            AtomicSwapState::Unassigned => None,
            // Safe because MaybeUninit<T> is transparent to T
            AtomicSwapState::Assigned(0) => Some(unsafe { &mut *(self.data.get() as *mut T) }),
            AtomicSwapState::Assigning | AtomicSwapState::Assigned(_) => {
                #[cfg(debug_assertions)]
                unreachable!("We should have exclusive access and therefore nothing should be assigning/reading");
                #[cfg(not(debug_assertions))]
                unsafe {
                    unreachable_unchecked()
                }
            }
        }
    }
    /// Gets a mutable reference to the current value if contains a value or fills with `value` then returns mutable reference to that.
    /// Alias to [`AtomicSwap::get_mut_or_else`]`(||value)`
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let mut swap = AtomicSwap::from_none();
    /// assert_eq!(swap.get_mut_or(100usize), &mut 100usize);
    /// assert_eq!(swap.get_mut_or(300usize), &mut 100usize);
    /// *swap.get_mut_or(400usize) = 200usize;
    /// assert_eq!(swap.take(), Some(200usize));
    /// ```
    #[inline]
    pub fn get_mut_or(&mut self, value: T) -> &mut T {
        self.get_mut_or_else(|| value)
    }
    /// Gets a mutable reference to the current value if contains a value or fills with `value()` then returns mutable reference to that.
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let mut swap = AtomicSwap::from_none();
    /// assert_eq!(swap.get_mut_or_else(||100usize), &mut 100usize);
    /// assert_eq!(swap.get_mut_or_else(||300usize), &mut 100usize);
    /// *swap.get_mut_or_else(||400usize) = 200usize;
    /// assert_eq!(swap.take(), Some(200usize));
    /// ```
    pub fn get_mut_or_else(&mut self, value: impl FnOnce() -> T) -> &mut T {
        match AtomicSwapState::from_usize(self.state.load(Ordering::Acquire)) {
            AtomicSwapState::Unassigned => {
                *self.data.get_mut() = MaybeUninit::new(value());
                self.state
                    .store(AtomicSwapState::Assigned(0).into_usize(), Ordering::Release);
            }
            AtomicSwapState::Assigned(0) => {}
            AtomicSwapState::Assigning | AtomicSwapState::Assigned(_) => {
                #[cfg(debug_assertions)]
                unreachable!("We should have exclusive access and therefore nothing should be assigning/reading");
                #[cfg(not(debug_assertions))]
                unsafe {
                    unreachable_unchecked()
                }
            }
        }
        // Safe because MaybeUninit<T> is transparent to T
        unsafe { &mut *(self.data.get() as *mut T) }
    }
    /// Gets a mutable reference to the current value if contains a value or fills with [`Default::default`] then returns mutable reference to that.
    /// Alias to [`AtomicSwap::get_mut_or_else`]`(T::default)`
    /// ```
    /// # use atomic_swap::AtomicSwap;
    /// let mut swap = AtomicSwap::from_none();
    /// assert_eq!(swap.get_mut_default(), &mut usize::default());
    /// *swap.get_mut_or_else(||400usize) = 200usize;
    /// assert_eq!(swap.get_mut_default(), &mut 200usize);
    /// assert_eq!(swap.take(), Some(200usize));
    /// ```
    #[inline]
    pub fn get_mut_default(&mut self) -> &mut T
    where
        T: Default,
    {
        self.get_mut_or_else(T::default)
    }
}
impl<T> Drop for AtomicSwap<T> {
    fn drop(&mut self) {
        match AtomicSwapState::from_usize(self.state.load(Ordering::Acquire)) {
            AtomicSwapState::Unassigned => {}
            AtomicSwapState::Assigning => {
                #[cfg(debug_assertions)]
                unreachable!("Should not have dropped while assigning!");
                #[cfg(not(debug_assertions))]
                unsafe {
                    unreachable_unchecked()
                }
            }
            AtomicSwapState::Assigned(0) => unsafe { drop(self.data.get().read().assume_init()) },
            AtomicSwapState::Assigned(_) => {
                #[cfg(debug_assertions)]
                unreachable!("Should not drop while has readers!");
                #[cfg(not(debug_assertions))]
                unsafe {
                    unreachable_unchecked()
                }
            }
        }
    }
}
impl<T> EnsureSend for AtomicSwap<T> where T: Send {}
unsafe impl<T> Sync for AtomicSwap<T> where T: Send {}
impl<T> Default for AtomicSwap<T> {
    #[inline]
    fn default() -> Self {
        Self::from_none()
    }
}

trait EnsureSend: Send {}

/// Does not implement [`From`] for [`usize`] to allow for const from functions
#[derive(Copy, Clone, Debug)]
enum AtomicSwapState {
    /// No current value
    Unassigned,
    /// Exclusive access
    Assigning,
    /// Num Readers
    Assigned(usize),
}
impl AtomicSwapState {
    pub const fn into_usize(self) -> usize {
        match self {
            AtomicSwapState::Unassigned => 0,
            AtomicSwapState::Assigning => 1,
            AtomicSwapState::Assigned(readers) => 2 + readers,
        }
    }

    pub const fn from_usize(size: usize) -> Self {
        match size {
            0 => Self::Unassigned,
            1 => Self::Assigning,
            x => Self::Assigned(x - 2),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::AtomicSwap;
    use rand::{thread_rng, Rng};
    use std::string::String;
    use std::sync::Arc;
    use std::thread::spawn;
    use std::vec::Vec;

    #[derive(Default, Debug, Eq, PartialEq, Clone)]
    struct ComplexType {
        string: String,
        number: usize,
        vector: Vec<i64>,
    }
    impl ComplexType {
        fn generate<R: Rng + ?Sized>(rng: &mut R) -> Self {
            let string_length = rng.gen_range(10..100);
            let mut string = String::with_capacity(string_length);
            let mut temp = [0; 4];
            for _ in 0..string_length {
                string += rng.gen::<char>().encode_utf8(&mut temp);
            }
            let vec_length = rng.gen_range(100..1000);
            let mut vector = Vec::with_capacity(vec_length);
            for _ in 0..vec_length {
                vector.push(rng.gen());
            }
            Self {
                string,
                number: rng.gen(),
                vector,
            }
        }
        fn generate_option<R: Rng + ?Sized>(rng: &mut R) -> Option<Self> {
            if rng.gen() {
                Some(Self::generate(rng))
            } else {
                None
            }
        }
    }

    #[test]
    fn slam_test() {
        const OPS_PER_THREAD: usize = 1 << 10;
        const NUM_THREADS: usize = 1 << 4;
        let mut rng = thread_rng();
        for round_num in 0..4 {
            let swap_value = match round_num {
                0 => Some(ComplexType::generate(&mut rng)),
                1 => None,
                _ => ComplexType::generate_option(&mut rng),
            };
            let swap = Arc::new(AtomicSwap::new(swap_value));
            let mut threads = Vec::with_capacity(NUM_THREADS);
            for _thread_num in 0..NUM_THREADS {
                let swap_clone = swap.clone();
                threads.push(spawn(move || {
                    let mut rng = thread_rng();
                    for _op_num in 0..OPS_PER_THREAD {
                        let operation = rng.gen_range(0..=3);
                        match operation {
                            0 => {
                                swap_clone.swap(ComplexType::generate_option(&mut rng));
                            }
                            1 => {
                                swap_clone.take();
                            }
                            2 => swap_clone.set(ComplexType::generate_option(&mut rng)),
                            3 => {
                                swap_clone.clone_inner();
                            }
                            _ => unreachable!(),
                        }
                    }
                }));
            }
            for thread in threads {
                thread.join().expect("Could not join");
            }
        }
    }

    #[test]
    fn value_test() {
        const NUM_OPS: usize = 1 << 10;
        let mut rng = thread_rng();
        for round_num in 0..4 {
            let mut last_value = match round_num {
                0 => Some(ComplexType::generate(&mut rng)),
                1 => None,
                _ => ComplexType::generate_option(&mut rng),
            };
            let mut swap = AtomicSwap::new(last_value.clone());
            let mut last_op = -1;
            for _op_num in 0..NUM_OPS {
                let operation = rng.gen_range(0..=6);
                match operation {
                    0 => {
                        let new_value = ComplexType::generate_option(&mut rng);
                        assert_eq!(
                            last_value,
                            swap.swap(new_value.clone()),
                            "Last op: {}",
                            last_op
                        );
                        last_value = new_value;
                    }
                    1 => {
                        assert_eq!(last_value, swap.take(), "Last op: {}", last_op);
                        last_value = None;
                    }
                    2 => {
                        last_value = ComplexType::generate_option(&mut rng);
                        swap.set(last_value.clone());
                    }
                    3 => {
                        assert_eq!(last_value, swap.clone_inner(), "Last op: {}", last_op);
                    }
                    4 => {
                        let swap_ref = swap.get_mut();
                        assert_eq!(swap_ref, last_value.as_mut(), "Last op: {}", last_op);
                        if let Some(swap_ref) = swap_ref {
                            *swap_ref = ComplexType::generate(&mut rng);
                            last_value = Some(swap_ref.clone());
                        }
                    }
                    5 => {
                        let possible_value = ComplexType::generate(&mut rng);
                        let swap_ref = swap.get_mut_or(possible_value.clone());
                        assert_eq!(
                            swap_ref,
                            &mut last_value.unwrap_or_else(|| possible_value.clone()),
                            "Last op: {}",
                            last_op
                        );
                        *swap_ref = possible_value.clone();
                        last_value = Some(possible_value);
                    }
                    6 => {
                        let swap_ref = swap.get_mut_default();
                        assert_eq!(
                            swap_ref,
                            &mut last_value.unwrap_or_default(),
                            "Last op: {}",
                            last_op
                        );
                        *swap_ref = ComplexType::generate(&mut rng);
                        last_value = Some(swap_ref.clone());
                    }
                    _ => unreachable!(),
                }
                last_op = operation;
            }
        }
    }
}
