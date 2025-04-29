# 4.0.0

- Implement `SignedBitCount` for signed integer types.
- Remove endianness requirement for `BitCounter`
- Optimize `BitRecorder` implementation to be much faster
- Optimize read/write_bytes to be much faster for un-aligned bytes
- Seal `Endianness` traits from further downstream implementation

# 3.2.0

- Implement `Integer` for `bool` and arrays of `Integer` types.
- Add a `read_const` method to `BitRead` for consisency with `BitWrite::write_const`.
- Widen unknown `BitCount` values to handle more edge cases.

# 3.1.0

- Implement `Integer` for the unsigned `NonZero` types.
- Add byte alignment convenience methods.
- Fix `BitCount.checked_sub` for consistency with `checked_add`.

