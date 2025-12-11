// Compute number of general recursive functions of a given size.

use clap::Parser;
use memoize::memoize;
use rug::{Float, Integer};

type BigInt = Integer;

#[memoize]
fn count(size: usize, arity: usize) -> BigInt {
    // println!("  count({}, {})", size, arity);
    if size == 0 {
        return BigInt::from(0);
    } else if size == 1 {
        // Atoms
        // Z^k and P^k_i forall 1 <= i <= k
        let mut total = BigInt::from(arity + 1);
        if arity == 1 {
            // S is only a 1-arity function
            total += 1;
        }
        // println!("  count({}, {}) = {}", size, arity, total);
        return total;
    } else {
        // Combinators
        let n = size - 1;

        // M(f)
        let mut total = count(n, arity + 1);
        // println!("    M(f) {}", total);

        // R(g,h)
        if arity >= 1 {
            for x in 1..n {
                // |g| = x, |f| = y
                let y = n - x;
                // println!("      R(g,h) {} {}", x, y);
                total += count(x, arity - 1) * count(y, arity + 1)
            }
            // println!("    R(g,h) {}", total);
        }

        // C(h, g_1, ..., g_m)
        for x in 1..=n {
            // |h| = x, sum |g_i| = y
            let y = n - x;
            // Disallow m=0: C(h)
            for m in 1..=y {
                // println!("      C(h,gs) {} {} {}", x, y, m);
                total += count(x, m) * count_many(y, arity, m);
                // println!("      C(h,gs) {}", total);
            }
        }
        // println!("  count({}, {}) = {}", size, arity, total);
        return total;
    }
}

#[memoize]
fn count_many(size: usize, arity: usize, num_funcs: usize) -> BigInt {
    // println!("  count_many({}, {}, {})", size, arity, num_funcs);
    if num_funcs > size {
        return BigInt::from(0);
    } else if num_funcs == 0 {
        if size == 0 {
            return BigInt::from(1);
        } else {
            return BigInt::from(0);
        }
    }
    let mut total = BigInt::from(0);
    if num_funcs >= 1 {
        for x in 1..=size {
            let y = size - x;
            // println!("    A {} {} {}", x, y, num_funcs - 1);
            total += count(x, arity) * count_many(y, arity, num_funcs - 1);
            // println!("    B {}", total);
        }
    }
    // println!("  count_many({}, {}, {}) = {}", size, arity, num_funcs, total);
    total
}

fn log2(n: &BigInt) -> f32 {
    Float::with_val(32, n).log2().to_f32()
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    max_size: usize,
    arity: usize,
}

fn main() {
    let args = Args::parse();

    for size in 1..=args.max_size {
        let total = count(size, args.arity);
        println!("T({:2}, {}): {:4.0} bits  {}", size, args.arity, log2(&total), total);
    }
}

// Without allowing C(h):
//
//  T(1,0) = 1: Z^0
//      T(1,1) = 3: Z^1, S, P^1_1
//      T(1,2) = 3: Z^2, P^2_1, P^2_2
//      T(1,k) = k+1: Z^k, P^k_i
//  T(2,0) = 3: M(T(1,1))
//      T(2,1) = 3: M(T(1,2))
//      T(2,k) = k+2: M(T(1,k+1))
//  T(3,0) = 6
//          3: M(T(2,1))
//          3: C(T(1,1), T(1,0))
//      T(3,1) = 16
//          4: M(T(2,2))
//          3: R(T(1,0), T(1,2))
//          9: C(T(1,1), T(1,1))
// T(4,0) = 31:
//      16: M(T(3,1))
//      9: C(T(1,1), T(2,0))
//      3: C(T(2,1), T(1,0))
//      3: C(T(1,1), T(1,0), T(1,0))
