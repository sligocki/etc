// === Final Statistics (peBBle(8), max_steps = 100) ===
// Total programs:         23,588,107
// Halted programs:        4,517,508 (19.15%)
// Infinite programs:      19,070,599 (80.85%)
// Unknown programs:       0 (0.00%)
// Max halting step count: 63
// Champion program:       00_11_03_21_50_30_24_01
// Wallclock runtime:      4.673s
// Throughput:             5,047,882 programs/s
//
// === Pipeline & Decider Performance ===
// Stage / Decider                      Run On     Split On       Halted          Inf     Total Time     Avg / Prog
// ----------------------------------------------------------------------------------------------------------------
// StaticBacktrack                  25,688,761            0            0    7,065,148         1.27 s          49 ns
// Simulation (100 steps)           18,623,613    2,100,654    4,517,508   10,806,942        51.12 s        2.74 µs
// Cycler (100 steps)                1,198,509            0            0      863,081         8.21 s        6.85 µs
// SeparatedComponents (100 steps)     335,428            0            0      330,496         1.25 s        3.72 µs
// CTL (100 steps, moduli=[1])           4,932            0            0        4,932      793.27 ms      160.84 µs
// ----------------------------------------------------------------------------------------------------------------
//
// === Cycler Proof Statistics (863,081 proved) ===
// Periods:          min = 1, avg = 3.4, max = 69
// Top periods:      p=2 (294,194), p=1 (167,303), p=3 (102,463), p=4 (86,322), p=5 (63,385)
// Displacements:    dx=0 (523,074), dx=1 (132,025), dx=-1 (108,632), dx=2 (48,472), dx=-2 (30,641)
//
// === SeparatedComponents Proof Statistics (330,496 proved) ===
// Periods:          min = 2, avg = 3.3, max = 27
// Top periods:      p=2 (137,277), p=3 (92,681), p=4 (44,065), p=5 (21,747), p=6 (16,544)
//
// === CTL Proof Statistics (4,932 proved) ===
// Steps:            min = 304, avg = 304.0, max = 304
// States:           min = 16, avg = 123.1, max = 173
// Floors:           floor=6 (4,932)
// Moduli:           mod=1 (4,932)

use pebble::enumeration::{run_enumeration_cli, CtlConfig, PipelineConfig, PipelineStage};

fn main() {
    let pipeline = PipelineConfig {
        stages: vec![
            PipelineStage::StaticBacktrack,
            PipelineStage::Simulation { steps: 100 },
            PipelineStage::Cycler { steps: 100 },
            PipelineStage::SeparatedComponents { steps: 100 },
            PipelineStage::Ctl(CtlConfig {
                steps: 100,
                moduli: vec![1],
                ..Default::default()
            }),
        ],
    };

    run_enumeration_cli(8, pipeline);
}
