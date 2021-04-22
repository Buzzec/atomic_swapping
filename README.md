# atomic_swap
An arbitrary type atomic storage with swap operations.

This is guaranteed lock-free where atomics will be guaranteed lock-free, however it is not guaranteed wait free. Some operations may spin for a short time.
All values will be properly dropped.

```rust
use atomic_swap::option::AtomicSwapOption;

fn main() {
  let swap = AtomicSwapOption::new(Some(100usize));
  assert_eq!(swap.clone_inner(), Some(100usize));
  assert_eq!(swap.take(), Some(100usize));
  assert_eq!(swap.take(), None);
  swap.set(Some(200usize));
  assert_eq!(swap.swap(Some(300usize)), Some(200usize));
  assert!(swap.contains_value());
  assert_eq!(swap.clone_inner(), Some(300usize));
}
```
## License
Licensed under either of

* Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
