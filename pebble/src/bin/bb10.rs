// === Final Statistics (peBBle(10), max_steps = 10000) ===
// Total programs:         12,375,976,129
// Halted programs:        2,198,068,964 (17.76%)
// Infinite programs:      10,177,907,165 (82.24%)
// Unknown programs:       0 (0.00%)
// Max halting step count: 5,778
// Champion program:       00_02_01_40_14_12_00_17_63_18
// Wallclock runtime:      7117.999s
// Throughput:             1,738,687 programs/s
// 
// === Pipeline & Decider Performance ===
// Stage / Decider                                          Run On     Split On         Halted            Inf     Total Time     Avg / Prog
// ----------------------------------------------------------------------------------------------------------------------------------------
// StaticBacktrack                                  13,176,285,367            0              0  2,876,013,874       977.30 s          74 ns
// Simulation (100 steps)                           10,300,271,493  800,308,821  2,198,067,738  6,562,243,904     42133.86 s        4.09 µs
// Cycler / TransCycler (100 steps)                    739,651,030          395          1,155    500,659,319      7332.25 s        9.91 µs
// SeparatedComponents (100 steps)                     238,990,161           11             43    234,415,235      1267.49 s        5.30 µs
// CTL (100 steps)                                       4,574,872            7             22      4,572,125       926.21 s      202.46 µs
// Bouncer (100 steps)                                       2,718            0              0          1,514      120.30 ms       44.26 µs
// Simulation (10000 steps)                                  1,204            4              6             78      885.32 ms      735.32 µs
// Cycler (10000 steps)                                      1,116            0              0            731         2.46 s        2.20 ms
// SeparatedComponents (10000 steps)                           385            0              0             19        25.34 s       65.81 ms
// CTL (10000 steps, states=4000, thresh=[2, 3], floors=[6, 8])366            0              0            366         6.88 s       18.81 ms
// ----------------------------------------------------------------------------------------------------------------------------------------
// 
// === Cycler Proof Statistics (500,660,050 proved) ===
// Periods:          min = 1, avg = 3.8, max = 208
// Top periods:      p=2 (179,403,873), p=1 (109,192,298), p=3 (45,053,960), p=4 (37,163,545)
// Displacements:    dx=0 (339,761,194), dx=1 (55,606,539), dx=-1 (48,736,351)
//
// === SeparatedComponents Proof Statistics (234,415,254 proved) ===
// Periods:          min = 1, avg = 4.0, max = 91
// Top periods:      p=2 (92,779,250), p=3 (56,517,243), p=4 (26,751,944), p=5 (16,134,909)
//
// === Bouncer Proof Statistics (1,514 proved) ===
// Bounce steps:     min = 12, avg = 16.5, max = 26
// Top bounce steps: s=15 (241), s=14 (224), s=16 (165), s=17 (161), s=19 (143), s=18 (141)
// Gap growths:      Δg=3 (888), Δg=4 (478), Δg=2 (77), Δg=5 (43), Δg=6 (15), Δg=7 (13)
//
// === CTL Proof Statistics (4,572,491 proved) ===
// Steps:            min = 304, avg = 306.4, max = 30,004
// States:           min = 1, avg = 37.8, max = 1,492
// Floors:           floor=6 (4,572,491)
// Moduli:           mod=1 (4,528,100), mod=2 (30,504), mod=3 (9,800), mod=4 (2,727), mod=6 (1,356), mod=12 (4)

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
                ..Default::default()
            }),
            PipelineStage::Bouncer { steps: 100 },
            PipelineStage::Simulation { steps: 10_000 },
            PipelineStage::Cycler { steps: 10_000 },
            PipelineStage::SeparatedComponents { steps: 10_000 },
            PipelineStage::Ctl(CtlConfig {
                steps: 10_000,
                max_states: 4_000,
                split_thresh: vec![2, 3],
                floors: vec![6, 8],
                ..Default::default()
            }),
        ],
    };

    run_enumeration_cli(10, pipeline);
}
