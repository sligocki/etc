/// Simulate the Ackermann worm on a list supplied on the command line.
///
/// Usage examples:
///   ack_worm 3
///   ack_worm 1 2
///   ack_worm --verbose 1 1 1
///
/// Algorithm:
///   N = 0
///   while list is not empty and not all zeros:
///     N += 1
///     k = pop_last(list)
///     if k > 0: append N copies of (k-1) to list
///   return N
use clap::Parser;

#[derive(Parser, Debug)]
#[command(
    about = "Simulate the Ackermann worm at the high level",
    long_about = "Runs the Ackermann worm algorithm on the given list.\n\
                  Algorithm:\n\
                  \x20 N = 0\n\
                  \x20 while list is not empty and not all zeros:\n\
                  \x20   N += 1; k = pop_last(list)\n\
                  \x20   if k > 0: append N copies of (k-1) to list\n\
                  \x20 return N"
)]
struct Args {
    /// The initial list (space-separated non-negative integers).
    list: Vec<u64>,

    /// Print the list state after every step.
    #[arg(short, long)]
    verbose: bool,

    /// Stop after this many steps (0 = unlimited).
    #[arg(long, default_value_t = 1_000_000_000)]
    max_steps: u64,
}

fn all_zeros(list: &[u64]) -> bool {
    list.iter().all(|&x| x == 0)
}

fn fmt_list(list: &[u64]) -> String {
    let inner: Vec<String> = list.iter().map(|x| x.to_string()).collect();
    format!("[{}]", inner.join(", "))
}

fn main() {
    let args = Args::parse();
    let mut list = args.list;
    let mut n: u64 = 0;

    if args.verbose {
        println!("{:>3}: {}", n, fmt_list(&list));
    }

    loop {
        if list.is_empty() || all_zeros(&list) {
            break;
        }
        if args.max_steps > 0 && n >= args.max_steps {
            if args.verbose {
                println!();
            }
            eprintln!("Stopped after {} steps (limit: {})", n, args.max_steps);
            std::process::exit(1);
        }

        n += 1;
        let k = list.pop().unwrap();
        if k > 0 {
            let appended = vec![k - 1; n as usize];
            list.extend_from_slice(&appended);
        }

        if args.verbose {
            println!("{:>3}: {}", n, fmt_list(&list));
        }
    }

    if args.verbose {
        println!();
    }
    println!("{}", n);
}
