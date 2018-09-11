bitstream-io
============

A Rust library for reading or writing binary values to or from streams
which may not be aligned at a whole byte.

This library is intended to be flexible enough to wrap
around any stream which implements the `Read` or `Write` traits.
It also supports a wide array of integer data types as
containers for those binary values.

[Documentation](https://docs.rs/bitstream-io/0.8.0/bitstream_io/)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
bitstream-io = "0.8"
```

and this to your crate root:

```rust
extern crate bitstream_io;
```
