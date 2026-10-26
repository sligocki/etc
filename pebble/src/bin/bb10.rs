// === Final Statistics (peBBle(10), max_steps = 10000) ===
// Total programs:         12,375,976,129
// Halted programs:        2,198,068,964 (17.76%)
// Infinite programs:      10,177,907,165 (82.24%)
// Unknown programs:       0 (0.00%)
// Max halting step count: 5,778
// Champion program:       00_02_01_40_14_12_00_17_63_18
// Wallclock runtime:      3456.729s
// Throughput:             3,580,256 programs/s
// 
// === Pipeline & Decider Performance ===
// Stage / Decider                                        Run On     Split On         Halted            Inf     Total Time     Avg / Prog
// --------------------------------------------------------------------------------------------------------------------------------------
// StaticBacktrack                                13,176,285,367            0              0  2,876,013,874       749.99 s          56 ns
// Simulation (100 steps)                         10,300,271,493  800,308,821  2,198,067,738  6,562,243,904     32187.03 s        3.12 µs
// Cycler (100 steps)                                739,651,030          395          1,155    500,659,319      5730.95 s        7.75 µs
// SeparatedComponents (100 steps)                   238,990,161           11             43    234,415,235      1009.22 s        4.22 µs
// CTL (100 steps)                                     4,574,872            7             22      4,572,125       682.62 s      149.21 µs
// Bouncer (100 steps)                                     2,718            0              0          1,514       41.84 ms       15.39 µs
// Simulation (10000 steps)                                1,204            4              6             78      424.78 ms      352.81 µs
// Cycler (10000 steps)                                    1,116            0              0            731      986.31 ms      883.79 µs
// SeparatedComponents (10000 steps)                         385            0              0             19        10.05 s       26.11 ms
// CTL (10000 steps, states=4000, thresh=[2, 3],
//      floors=[6, 8, 10])                                   366            0              0            366         3.44 s        9.39 ms
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
