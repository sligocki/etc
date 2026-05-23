use gen_rec::closed_form_enum::{ClosedFormEnumerator, EnumMode};
use gen_rec::grf::Grf;

fn main() {
    let alt = "C(P(2,2), C(S, Z0), Z0)".parse::<Grf>().unwrap();
    for dyn_rnf in [false, true] {
        let mut en =
            ClosedFormEnumerator::with_pruning(EnumMode::AllGrf, false).with_dynamic_rnf(dyn_rnf);
        en.prepare(0, 5);
        let mut found = false;
        en.for_each_raw_candidate(0, 5, &mut |c| {
            if c == &alt {
                found = true;
            }
        });
        println!("dynamic_rnf={} -> alt generated? {}", dyn_rnf, found);
    }
}
