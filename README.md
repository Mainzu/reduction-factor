# Reduction Factor

[![crates.io](https://img.shields.io/crates/v/reduction-factor.svg)](https://crates.io/crates/reduction-factor)
[![docs.rs](https://docs.rs/reduction-factor/badge.svg)](https://docs.rs/reduction-factor)

A tiny, `#![no_std]`-compatible crate for representing and correctly composing reduction factors, like discounts or damage resistance.

## What is a Reduction Factor?

A `Reduction<T>` is a newtype wrapper around a value `x` of type `T` that semantically represents a multiplicative factor of `1 - x`.

This is useful for modeling concepts like:

- A **25% discount**: `Reduction(0.25)`, which applies a multiplier of `0.75`.
- **10% damage resistance**: `Reduction(0.10)`, which means you take `0.90` times the damage.
- A **10% chance of failure**: `Reduction(0.10)`, which represents a success rate of `0.90`.

The main benefit of this wrapper type is ensuring that multiple reductions are **composed** (or "stacked") correctly.

## Key Features

- **Correct Composition**: Prevents the common bug of simply adding percentages. Applying a 20% reduction and then a 10% reduction is **not** a 30% reduction, but a 28% one.
- **Ergonomic API**: Use the multiplication operator (`*`) to stack reductions or apply them to values, making your code clear and intuitive.
- **Generic**: Works with any numeric type that supports the required traits (e.g., `f32`, `f64`, or custom fixed-point types for applications requiring perfect precision).
- **Zero-cost**: As a simple newtype wrapper, `Reduction<T>` has the same memory layout and performance as the underlying type `T`.
- **`no_std` compatible**: Usable in embedded, WASM, and other resource-constrained environments.

## Examples

Create a `Reduction` and apply it to a value using the `*` operator or the `reduce` method.

```rust
use reduction_factor::Reduction;

let discount = Reduction::new(0.25f32); // A 25% reduction
let price = 100.0;

// This calculates `price * (1.0 - 0.25)`
let final_price = discount * price;
assert_eq!(final_price, 75.0);

// You can also use the `reduce` method for clarity
assert_eq!(discount.reduce(price), 75.0);
```

### Composing Reductions

This is the core feature of the crate. When you multiply two `Reduction`s, they are composed mathematically correctly.

The composition logic is derived from the multiplicative nature of reductions. Applying a reduction `x` followed by a reduction `y` is equivalent to multiplying by `(1 - x)` and then by `(1 - y)`. The combined multiplier is `(1 - x) * (1 - y)`, which simplifies to `1 - (x + y - xy)`. The `Reduction` type handles this calculation automatically when you use the multiplication operator.

For a concrete example of combining 20% and 10% reductions on a value of 100:

1. Applying the first reduction: `100 * (1 - 0.20) = 80`
2. Applying the second reduction: `80 * (1 - 0.10) = 72`
3. The total reduction is `100 - 72 = 28`, which is a `28%` reduction, not `30%`.

The `Reduction` type makes this effortless:

```rust
use reduction_factor::Reduction;

let armor_resistance = Reduction(0.20); // 20%
let magic_shield = Reduction(0.10);     // 10%

// Combine the two reductions using multiplication
let total_resistance = armor_resistance * magic_shield;

// The combined reduction is 0.28, or 28%
assert_eq!(*total_resistance, 0.28);

let incoming_damage = 100.0;
let damage_taken = total_resistance * incoming_damage;

assert_eq!(damage_taken, 72.0);
```

The multiplication operator (`*`) is used for this composition because the operation is **commutative** (order doesn't matter) and **associative** (grouping doesn't matter), just like standard multiplication.

### Special Values

- **`Reduction::none()`**: A 0% reduction (`Reduction(0)`). This is the **multiplicative identity** for composition. Any reduction composed with `none()` remains unchanged. It is also the `Default`.
- **`Reduction::full()`**: A 100% reduction (`Reduction(1)`). This is the **absorbing element** (or annihilator). Any reduction composed with `full()` becomes a `full()` reduction.

```rust
use reduction_factor::Reduction;

// Identity element
let no_change = Reduction::none(); // 0%
let r = Reduction(0.25);
assert_eq!(r * no_change, r);

// Absorbing element
let full_reduction = Reduction::full(); // 100%
// Note: Floating point precision may affect exact equality checks.
assert_eq!(r * full_reduction, full_reduction);
assert_eq!(full_reduction * 50.0, 0.0);
```
