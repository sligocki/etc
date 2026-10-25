// === Final Statistics (peBBle(10), max_steps = 1000000) ===
// Total programs:         12,375,976,129
// Halted programs:        2,198,068,964 (17.76%)
// Infinite programs:      10,177,905,644 (82.24%)
// Unknown programs:       1,521 (0.00%)
// Max halting step count: 5,778
// Champion program:       00_02_01_40_14_12_00_17_63_18
// Wallclock runtime:      92887.441s
// Throughput:             133,236 programs/s
// 
// === Pipeline & Decider Performance ===
// Stage / Decider                                        Run On     Split On       Halted          Inf     Total Time     Avg / Prog
// ------------------------------------------------------------------------------------------------------------------------
// StaticBacktrack                                  13,176,285,367            0            0 2,876,013,874       977.30 s          74 ns
// Simulation (100 steps)                           10,300,271,493  800,308,821 2,198,067,738 6,562,243,904     42133.86 s        4.09 µs
// Cycler / TransCycler (100 steps)                  739,651,030          395        1,155  500,659,319      7332.25 s        9.91 µs
// SeparatedComponents (100 steps)                   238,990,161           11           43  234,415,235      1267.49 s        5.30 µs
// CTL (100 steps)                                     4,574,872            7           22    4,572,125       926.21 s      202.46 µs
// Simulation (10000 steps)                                2,718            4            6           78         1.25 s      459.25 µs
// Cycler / TransCycler (10000 steps)                      2,630            0            0          731         6.56 s        2.49 ms
// SeparatedComponents (10000 steps)                       1,899            0            0           19        45.95 s       24.20 ms
// CTL (10000 steps, states=4000, floors=[6, 8])           1,880            0            0          359      4466.62 s         2.38 s
// Simulation (1000000 steps)                              1,521            0            0            0        65.04 s       42.76 ms
// Cycler / TransCycler (1000000 steps)                    1,521            0            0            0       825.59 s      542.80 ms
// SeparatedComponents (1000000 steps)                     1,521            0            0            0     14837.44 s         9.76 s
// CTL (1000000 steps, states=20000, floors=[6, 8, 10, 12])        1,521            0            0            0    934776.12 s       614.58 s
// ------------------------------------------------------------------------------------------------------------------------
// 
// === CTL Proof Statistics (4,572,484 proved) ===
// Steps:            min = 304, avg = 306.4, max = 30,004
// States:           min = 1, avg = 37.8, max = 2,376
// Floors:           floor=6 (4,572,484)
// Moduli:           mod=1 (4,528,090), mod=2 (30,507), mod=3 (9,800), mod=4 (2,727), mod=6 (1,356), mod=12 (4)

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
                moduli: vec![1, 2, 3, 4, 6, 12],
            },
            PipelineStage::Simulation { steps: 10_000 },
            PipelineStage::Cycler { steps: 10_000 },
            PipelineStage::SeparatedComponents { steps: 10_000 },
            PipelineStage::Ctl {
                steps: 10_000,
                max_states: 4_000,
                floors: vec![6, 8],
                moduli: vec![1, 2, 3, 4, 6, 12],
            },
            PipelineStage::Simulation { steps: 1_000_000 },
            PipelineStage::Cycler { steps: 1_000_000 },
            PipelineStage::SeparatedComponents { steps: 1_000_000 },
            PipelineStage::Ctl {
                steps: 1_000_000,
                max_states: 20_000,
                floors: vec![6, 8, 10, 12],
                moduli: vec![1, 2, 3, 4, 6, 12],
            },
        ],
    };

    run_enumeration_cli(10, pipeline);
}
