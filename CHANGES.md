# 3.2.0

- Implement `Integer` for `bool` and arrays of `Integer` types.
- Add a `read_const` method to `BitRead` for consisency with `BitWrite::write_const`.
- Widen unknown `BitCount` values to handle more edge cases.

# 3.1.0

- Implement `Integer` for the unsigned `NonZero` types.
- Add byte alignment convenience methods.
- Fix `BitCount.checked_sub` for consistency with `checked_add`.

