//! A concurrent data structure that allows for [`AtomicSwap::swap`] operations to be run on any type `T`.
//! ```
//! use atomic_swapping::AtomicSwap;
//!
//! let swap = AtomicSwap::new(100usize);
//! assert_eq!(swap.clone_inner(), 100usize);
//! assert_eq!(swap.swap(300usize), 100usize);
//! assert_eq!(swap.clone_inner(), 300usize);
//! ```
//! This is guaranteed lock-free where atomics will be guaranteed lock-free, however it is not guaranteed wait free. Some operations may spin for a short time.
//! All values will be properly dropped.
#![warn(missing_debug_implementations, missing_docs, unused_import_braces)]
#![cfg_attr(not(test), no_std)]

pub mod option;

use core::cell::UnsafeCell;
use core::hint::spin_loop;
#[cfg(not(debug_assertions))]
use core::hint::unreachable_unchecked;
use core::mem::swap;
use core::sync::atomic::{AtomicUsize, Ordering};

/// Allows shared access to `T` by only swap related operations. Acts like it stores an [`Option<T>`]
/// ```
/// use atomic_swapping::AtomicSwap;
///
/// let swap = AtomicSwap::new(100usize);
/// assert_eq!(swap.clone_inner(), 100usize);
/// assert_eq!(swap.swap(300usize), 100usize);
/// assert_eq!(swap.clone_inner(), 300usize);
/// ```
#[derive(Debug)]
pub struct AtomicSwap<T> {
    state: AtomicUsize,
    data: UnsafeCell<T>,
}
impl<T> AtomicSwap<T> {
    /// Creates a new [`AtomicSwap`] from a value.
    /// ```
    /// # use atomic_swapping::AtomicSwap;
    /// let some_swap = AtomicSwap::new(100usize);
    /// assert_eq!(some_swap.swap(200usize), 100usize);
    /// ```
    pub const fn new(value: T) -> Self {
        Self {
            state: AtomicUsize::new(AtomicSwapState::Assigned(0).into_usize()),
            data: UnsafeCell::new(value),
        }
    }

    /// Swaps the current value in the swap with `value`, returning the currently contained value.
    /// Same as [`AtomicSwap::swap_hint`] with [`spin_loop`] as `spin_loop_hint`.
    /// ```
    /// # use atomic_swapping::AtomicSwap;
    /// let swap = AtomicSwap::new(100usize);
    /// assert_eq!(swap.swap(200usize), 100usize);
    /// assert_eq!(swap.swap(300usize), 200usize);
    /// ```
    #[inline]
    pub fn swap(&self, value: T) -> T {
        self.swap_hint(value, spin_loop)
    }
    /// Swaps the current value in the swap with `value`, returning the currently contained value.
    /// Same as [`AtomicSwap::swap`] but with a custom spin loop hint function.
    /// ```
    /// # use atomic_swapping::AtomicSwap;
    /// let swap = AtomicSwap::new(100usize);
    /// let spin_hint = ||println!("I'm spinning! Probably should yield here.");
    /// assert_eq!(swap.swap_hint(200usize, spin_hint), 100usize);
    /// assert_eq!(swap.swap_hint(300usize, spin_hint), 200usize);
    /// ```
    pub fn swap_hint(&self, mut value: T, mut spin_loop_hint: impl FnMut()) -> T {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            let state_enum = AtomicSwapState::from_usize(state);
            match &state_enum {
                AtomicSwapState::Assigned(0) => {
                    match self.state.compare_exchange_weak(
                        state,
                        AtomicSwapState::Assigning.into_usize(),
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            unsafe {
                                swap(&mut value, &mut *self.data.get());
                            };
                            self.state
                                .compare_exchange(
                                    AtomicSwapState::Assigning.into_usize(),
                                    AtomicSwapState::Assigned(0).into_usize(),
                                    Ordering::AcqRel,
                                    Ordering::Acquire,
                                )
                                .expect("Assigning was changed improperly!");
                            return value;
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
    /// # use atomic_swapping::AtomicSwap;
    /// let swap = AtomicSwap::new(100usize);
    /// assert_eq!(swap.clone_inner(), 100usize);
    /// assert_eq!(swap.swap(200usize), 100usize);
    /// assert_eq!(swap.clone_inner(), 200usize);
    /// ```
    #[inline]
    pub fn clone_inner(&self) -> T
    where
        T: Clone + Sync,
    {
        self.clone_inner_hint(spin_loop)
    }
    /// Clones the contained value if [`Some`] and returns it. `T` must be [`Clone`] and [`Sync`] because multiple threads could clone this simultaneously.
    /// Same as [`AtomicSwap::clone_inner`] but with a custom spin loop hint function.
    /// ```
    /// # use atomic_swapping::AtomicSwap;
    /// let swap = AtomicSwap::new(100usize);
    /// let spin_hint = ||println!("I'm spinning! Probably should yield here.");
    /// assert_eq!(swap.clone_inner_hint(spin_hint), 100usize);
    /// assert_eq!(swap.swap_hint(200usize, spin_hint), 100usize);
    /// assert_eq!(swap.clone_inner_hint(spin_hint), 200usize);
    /// ```
    pub fn clone_inner_hint(&self, mut spin_loop_hint: impl FnMut()) -> T
    where
        T: Clone + Sync,
    {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            match AtomicSwapState::from_usize(state) {
                AtomicSwapState::Assigned(readers) => match self.state.compare_exchange_weak(
                    state,
                    AtomicSwapState::Assigned(readers + 1).into_usize(),
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => unsafe {
                        // safe because MaybeUninit<T> is transparent to T while init
                        let out = (&*(self.data.get())).clone();
                        let result = self.state.fetch_sub(1, Ordering::AcqRel);
                        debug_assert_ne!(result, 0);
                        return out;
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

    /// Gets the internal value exclusively.
    /// ```
    /// # use atomic_swapping::AtomicSwap;
    /// let mut swap = AtomicSwap::new(100);
    /// assert_eq!(swap.get_mut(), &mut 100usize);
    /// *swap.get_mut() = 200usize;
    /// assert_eq!(swap.swap(300usize), 200usize);
    /// assert_eq!(swap.get_mut(), &mut 300usize);
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        match AtomicSwapState::from_usize(self.state.load(Ordering::Acquire)) {
            // Safe because MaybeUninit<T> is transparent to T
            AtomicSwapState::Assigned(0) => unsafe { &mut *(self.data.get() as *mut T) },
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
}
impl<T> Drop for AtomicSwap<T> {
    fn drop(&mut self) {
        match AtomicSwapState::from_usize(self.state.load(Ordering::Acquire)) {
            AtomicSwapState::Assigning => {
                #[cfg(debug_assertions)]
                unreachable!("Should not have dropped while assigning!");
                #[cfg(not(debug_assertions))]
                unsafe {
                    unreachable_unchecked()
                }
            }
            // UnsafeCell will drop properly
            AtomicSwapState::Assigned(0) => {}
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
impl<T> Default for AtomicSwap<T>
where
    T: Default,
{
    #[inline]
    fn default() -> Self {
        Self::new(T::default())
    }
}

trait EnsureSend: Send {}

/// Does not implement [`From`] for [`usize`] to allow for const from functions
#[derive(Copy, Clone, Debug)]
enum AtomicSwapState {
    /// Exclusive access
    Assigning,
    /// Num Readers
    Assigned(usize),
}
impl AtomicSwapState {
    pub const fn into_usize(self) -> usize {
        match self {
            AtomicSwapState::Assigning => 0,
            AtomicSwapState::Assigned(readers) => 1 + readers,
        }
    }

    pub const fn from_usize(size: usize) -> Self {
        match size {
            0 => Self::Assigning,
            x => Self::Assigned(x - 1),
        }
    }
}

#[cfg(test)]
pub mod test {
    use crate::AtomicSwap;
    use rand::{thread_rng, Rng};
    use std::string::String;
    use std::sync::Arc;
    use std::thread::spawn;
    use std::vec::Vec;

    #[derive(Default, Debug, Eq, PartialEq, Clone)]
    pub struct ComplexType {
        string: String,
        number: usize,
        vector: Vec<i64>,
    }
    impl ComplexType {
        pub fn generate<R: Rng + ?Sized>(rng: &mut R) -> Self {
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
        pub fn generate_option<R: Rng + ?Sized>(rng: &mut R) -> Option<Self> {
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
        for _round_num in 0..4 {
            let swap = Arc::new(AtomicSwap::new(ComplexType::generate(&mut rng)));
            let mut threads = Vec::with_capacity(NUM_THREADS);
            for _thread_num in 0..NUM_THREADS {
                let swap_clone = swap.clone();
                threads.push(spawn(move || {
                    let mut rng = thread_rng();
                    for _op_num in 0..OPS_PER_THREAD {
                        let operation = rng.gen_range(0..=1);
                        match operation {
                            0 => {
                                swap_clone.swap(ComplexType::generate(&mut rng));
                            }
                            1 => {
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
        for _round_num in 0..4 {
            let mut last_value = ComplexType::generate(&mut rng);
            let mut swap = AtomicSwap::new(last_value.clone());
            let mut last_op = -1;
            for _op_num in 0..NUM_OPS {
                let operation = rng.gen_range(0..=2);
                match operation {
                    0 => {
                        let new_value = ComplexType::generate(&mut rng);
                        assert_eq!(
                            last_value,
                            swap.swap(new_value.clone()),
                            "Last op: {}",
                            last_op
                        );
                        last_value = new_value;
                    }
                    1 => {
                        assert_eq!(last_value, swap.clone_inner(), "Last op: {}", last_op);
                    }
                    2 => {
                        let swap_ref = swap.get_mut();
                        assert_eq!(swap_ref, &mut last_value, "Last op: {}", last_op);
                        *swap_ref = ComplexType::generate(&mut rng);
                        last_value = swap_ref.clone();
                    }
                    _ => unreachable!(),
                }
                last_op = operation;
            }
        }
    }
}
