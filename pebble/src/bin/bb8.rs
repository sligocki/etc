// === Final Statistics (peBBle(8), max_steps = 100) ===
// Total programs:         23,588,107
// Halted programs:        4,517,508 (19.15%)
// Infinite programs:      19,070,599 (80.85%)
// Unknown programs:       0 (0.00%)
// Max halting step count: 63
// Champion program:       00_11_03_21_50_30_24_01
// Wallclock runtime:      16.071s
// Throughput:             1,467,727 programs/s
//
// === Pipeline & Decider Performance ===
// Stage / Decider                                        Run On     Split On       Halted          Inf     Total Time     Avg / Prog
// ------------------------------------------------------------------------------------------------------------------------
// StaticBacktrack                                    25,688,761            0            0    7,065,148         5.09 s         198 ns
// Simulation (100 steps)                             18,623,613    2,100,654    4,517,508   10,806,942       176.89 s        9.50 µs
// Cycler / TransCycler (100 steps)                    1,198,509            0            0      863,081        26.65 s       22.23 µs
// SeparatedComponents (100 steps)                       335,428            0            0      330,496         4.57 s       13.61 µs
// CTL (100 steps, moduli=[1])                             4,932            0            0        4,932         2.52 s      511.70 µs
// ------------------------------------------------------------------------------------------------------------------------
//
// === CTL Proof Statistics (4,932 proved) ===
// Steps:            min = 304, avg = 304.0, max = 304
// States:           min = 16, avg = 123.1, max = 173
// Floors:           floor=6 (4,932)
// Moduli:           mod=1 (4,932)

use pebble::enumeration::{run_enumeration_cli, PipelineConfig, PipelineStage};

fn main() {
    let pipeline = PipelineConfig {
        stages: vec![
            PipelineStage::StaticBacktrack,
            PipelineStage::Simulation { steps: 100 },
            PipelineStage::Cycler { steps: 100 },
            PipelineStage::SeparatedComponents { steps: 100 },
            PipelineStage::Ctl {
                steps: 100,
                max_states: 1024,
                floors: vec![6],
                moduli: vec![1],
            },
        ],
    };

    run_enumeration_cli(8, pipeline);
}
