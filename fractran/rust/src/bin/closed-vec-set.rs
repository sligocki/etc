use fractran::closed_vec_set::{ClosureResult, closure};
use fractran::vec_set::UnionVecSet;
use fractran::{prog, vec_set};

fn main() {
    // A complex Collatz-like non-halting program.
    // [2/45, 25/6, 343/2, 9/7, 2/3]
    let p = prog![
         1, -2, -1,  0;
        -1, -1,  2,  0;
        -1,  0,  0,  3;
         0,  2,  0, -1;
         1, -1,  0,  0;
    ];

    let seed = UnionVecSet::new(vec![
        vec_set!["10+", "0+", "0", "0"],
        vec_set!["0+", "0", "0+", "24+"],
        vec_set!["0", "46+", "0", "0+"],
    ]);
    let result = closure(&p, &seed, 100);
    if let ClosureResult::Closed(tree) = result {
        println!("CVS size: {}", tree.len());
        println!("{}", tree);
    } else {
        println!("Failed");
    }
}
