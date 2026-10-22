// === Final Statistics (peBBle(9), max_steps = 100000) ===
// Total programs:         528,594,612
// Halted programs:        93,824,392 (17.75%)
// Infinite programs:      434,770,220 (82.25%)
// Unknown programs:       0 (0.00%)
// Max halting step count: 63,577
// Champion program:       00_20_10_04_41_21_00_25_18
// Wallclock runtime:      180.276s
// Throughput:             2,932,143 programs/s
//
// === Pipeline & Decider Performance ===
// Stage / Decider                                        Run On     Split On       Halted          Inf     Total Time     Avg / Prog
// ------------------------------------------------------------------------------------------------------------------------
// StaticBacktrack                                   568,498,400            0            0  140,745,964        46.00 s          80 ns
// Simulation (100 steps)                            427,752,436   39,903,746   93,824,350  260,543,913      1927.56 s        4.51 µs
// Cycler / TransCycler (100 steps)                   33,480,427           13           13   23,039,829       382.15 s       11.41 µs
// SeparatedComponents (100 steps)                    10,440,572            2            2   10,232,435        68.21 s        6.53 µs
// CTL (100 steps)                                       208,133            7            7      208,079        14.28 s       68.59 µs
// Simulation (100000 steps)                                  40           20           20            0       13.37 ms      334.16 µs
// ------------------------------------------------------------------------------------------------------------------------
//
// === CTL Proof Statistics (208,079 proved) ===
// Steps:            min = 304, avg = 304.0, max = 308
// States:           min = 1, avg = 12.2, max = 645
// Floors:           floor=6 (208,079)
// Moduli:           mod=1 (207,948), mod=2 (108), mod=3 (23)

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
                moduli: vec![1, 2, 3],
            },
            PipelineStage::Simulation { steps: 100_000 },
        ],
    };

    run_enumeration_cli(9, pipeline);
}
