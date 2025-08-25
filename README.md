# Reduction Factor

[![crates.io](https://img.shields.io/crates/v/reduction_factor.svg)](https://crates.io/crates/reduction_factor)
[![docs.rs](https://docs.rs/reduction_factor/badge.svg)](https://docs.rs/reduction_factor)

A tiny, `#![no_std]`-compatible crate for representing and correctly composing reduction factors, like discounts or damage resistance.

## What is a Reduction Factor?

A `Reduction<T>` is a wrapper around a value `x` of type `T` that semantically represents a multiplicative factor of `(1 - x)`.

This is useful for modeling concepts like:

- A **25% discount**: `Reduction(0.25f32)`, which applies a multiplier of `0.75`.
- **10% damage resistance**: `Reduction(0.10f32)`, which means you take `0.90` times the damage.
- **90% chance of sucess**: `Reduction(0.90f64)`, which means the failure chance is `0.10`.

The primary benefit of this type is its ability to correctly **compose** (or stack) multiple reductions.

## Key Features

- **Correct Composition**: Prevents the common bug of simply adding percentages. Applying a 20% reduction and then a 10% reduction is **not** a 30% reduction, but a 28% one. This crate's `*` operator handles this correctly.
- **Ergonomic API**: Use `*` to stack reductions or apply them to values.
- **Type-Safe**: Clearly distinguishes between the reduction value (`0.25`) and the final multiplier (`0.75`), improving code clarity.
- **Generic**: Works with any numeric type that supports the required traits (e.g., `f32`, `f64`, custom fixed-point types).
- **`no_std` compatible**: Usable in embedded and WASM environments.

## Usage

### Basic Creation and Application

Create a `Reduction` and apply it to a value.

```rust
use reduction_factor::Reduction;

// A 25% discount
let discount = Reduction::new(0.25f32);

// The price of an item
let price = 100.0;

// Apply the discount
// This calculates `price * (1.0 - 0.25)`
let final_price = discount * price;

assert_eq!(final_price, 75.0);

// You can also use the `reduce` method
assert_eq!(discount.reduce(price), 75.0);
```

### Stacking Reductions

This is the main power of the crate. When you multiply two `Reduction`s, they are composed correctly.

**The wrong way (simple addition):**
`20% + 10% = 30%` reduction. Price: `100.0 * (1.0 - 0.30) = 70.0`. **Incorrect!**

**The right way (sequential application):**
`100.0 * (1.0 - 0.20) = 80.0`
`80.0 * (1.0 - 0.10) = 72.0`
This is a total reduction of 28%.

The `Reduction` type handles this automatically with the `*` operator.

```rust
use reduction_factor::Reduction;

let armor_resistance = Reduction(0.20f32); // 20%
let magic_shield = Reduction(0.10f32);   // 10%

// Stack the two reductions
// This calculates: 1 - (1 - 0.20) * (1 - 0.10) = 1 - 0.8 * 0.9 = 1 - 0.72 = 0.28
let total_resistance = armor_resistance * magic_shield;

assert_eq!(*total_resistance, 0.28);

let incoming_damage = 100.0;
let damage_taken = total_resistance * incoming_damage;

assert_eq!(damage_taken, 72.0);
```

### Special Values

- **`Reduction::none()`**: A 0% reduction (`Reduction(0.0)`). This is the **multiplicative identity** for stacking. Any reduction stacked with `none()` remains unchanged. It is also the `Default`.
- **`Reduction::full()`**: A 100% reduction (`Reduction(1.0)`). This is the **absorbing element** (or annihilator). Any reduction stacked with `full()` becomes a `full()` reduction.

```rust
use reduction_factor::Reduction;

// Identity element
let no_change = Reduction::none();
let r = Reduction(0.25);
assert_eq!(r * no_change, r);

// Absorbing element
let full_reduction = Reduction::full();
assert_eq!(r * full_reduction, full_reduction);
assert_eq!(full_reduction * 50.0, 0.0);
```
