use std::env;

use fractran::parse::load_program;
use fractran::program::State;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <programs_file>[:<record_num>]", args[0]);
        std::process::exit(1);
    }
    let filename_record = &args[1];
    let prog = load_program(filename_record).expect("Couldn't load program from file");
    let state = State::start(&prog);

    println!("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
    println!("<pnml xmlns=\"http://www.pnml.org/version-2009/grammar/pnml\">");
    println!(" <net id=\"pvas_net\" type=\"http://www.pnml.org/version-2009/grammar/ptnet\">");
    println!("  <page id=\"page0\">");

    // PLACES (Registers)
    for (i, init_val) in state.data.iter().enumerate() {
        println!("   <place id=\"p{}\">", i);
        println!("    <name><text>p{}</text></name>", i);
        println!(
            "    <initialMarking><text>{}</text></initialMarking>",
            init_val
        );
        // Visual layout hint (simple horizontal spread)
        println!(
            "    <graphics><position x=\"{}\" y=\"100\"/></graphics>",
            100 + (i * 80)
        );
        println!("   </place>");
    }

    // TRANSITIONS
    for r in 0..prog.num_instrs() {
        println!("   <transition id=\"t{}\">", r);
        // Tapaal/LoLA use the name to identify the transition
        println!("    <name><text>t{}</text></name>", r);
        println!(
            "    <graphics><position x=\"{}\" y=\"200\"/></graphics>",
            100 + (r * 80)
        );
        println!("   </transition>");
    }

    // ARCS (Transition instrs)
    let mut arc_num = 0;
    for (instr_num, instr) in prog.instrs.iter().enumerate() {
        for (place_num, delta) in instr.data.iter().enumerate() {
            if *delta < 0 {
                // CONSUME: Place -> Transition
                println!(
                    "   <arc id=\"a{}\" source=\"p{}\" target=\"t{}\">",
                    arc_num, place_num, instr_num
                );
                println!("    <inscription><text>{}</text></inscription>", -delta);
                println!("   </arc>");
                arc_num += 1;
            } else if *delta > 0 {
                // PRODUCE: Transition -> Place
                println!(
                    "   <arc id=\"a{}\" source=\"t{}\" target=\"p{}\">",
                    arc_num, instr_num, place_num
                );
                println!("    <inscription><text>{}</text></inscription>", delta);
                println!("   </arc>");
                arc_num += 1;
            }
        }
    }

    println!("  </page>");
    println!(" </net>");
    println!("</pnml>");
}
