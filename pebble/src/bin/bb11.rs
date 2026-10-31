// === Final Statistics (peBBle(11), max_steps = 10000000) ===
// Total programs:         352,152,122,808
// Halted programs:        57,943,096,570 (16.45%)
// Infinite programs:      294,208,666,532 (83.55%)
// Unknown programs:       359,706 (0.00%)
// Max halting step count: 9,040,389
// Champion program:       00_00_03_04_01_10_61_80_27_00_02
// Wallclock runtime:      158915.990s
// Throughput:             2,215,964 programs/s
//
// === Pipeline & Decider Performance ===
// Stage / Decider                             Run On        Split On          Halted              Inf     Total Time     Avg / Prog
// ---------------------------------------------------------------------------------------------------------------------------------
// StaticBacktrack                    371,924,569,856               0               0   73,479,119,137     24100.84 s          64 ns
// Simulation (100 steps)             298,445,450,719  19,772,289,809  57,942,705,629  196,253,448,038   1039869.39 s        3.48 µs
// Cycler (100 steps)                  24,477,007,243         141,961         356,991   15,873,231,375    216251.59 s        8.83 µs
// SeparatedComponents (100 steps)      8,603,276,916           6,118          10,923    8,390,084,462     44284.98 s        5.15 µs
// CTL (100 steps)                        213,175,413           3,220           4,893      209,164,681    301988.72 s        1.42 ms
// Bouncer (100 steps)                      4,002,619               0               0           46,910        61.82 s       15.45 µs
// Simulation (10000 steps)                 3,955,709           4,868          13,255            6,899      1534.01 s      387.80 µs
// Cycler (10000 steps)                     3,930,687             141             531        3,463,282      1449.59 s      368.79 µs
// SeparatedComponents (10000 steps)          466,733             125             607          100,131     12916.51 s       27.67 ms
// Simulation (10000000 steps)                365,870             806           3,741            1,617    148435.90 s      405.71 ms
// ---------------------------------------------------------------------------------------------------------------------------------
//
// === Cycler Proof Statistics (15,876,694,657 proved) ===
// Periods:          min = 1, avg = 4.3, max = 7,092
// Top periods:      p=2 (5,757,002,459), p=1 (3,280,743,491), p=3 (1,241,210,389), p=4 (1,044,374,780), p=5 (680,004,340), p=6 (653,550,325), p=7 (543,303,558), p=8 (472,454,225)
// Displacements:    dx=0 (10,995,072,871), dx=1 (1,499,088,562), dx=-1 (1,325,163,259), dx=2 (670,963,376), dx=-2 (548,691,008), dx=3 (261,922,639), dx=-3 (198,952,646), dx=4 (111,565,115)
//
// === SeparatedComponents Proof Statistics (8,390,184,593 proved) ===
// Periods:          min = 1, avg = 4.0, max = 119
// Top periods:      p=2 (3,230,941,315), p=3 (2,182,610,138), p=4 (862,267,844), p=5 (549,005,872), p=6 (514,238,762), p=7 (286,379,618), p=8 (170,222,850), p=9 (155,005,437)
//
// === Bouncer Proof Statistics (46,910 proved) ===
// Bounce steps:     min = 10, avg = 21.2, max = 77
// Top bounce steps: s=22 (5,175), s=17 (5,022), s=19 (4,102), s=21 (3,705), s=20 (3,338), s=23 (2,878), s=16 (2,867), s=24 (2,652)
// Gap growths:      Δg=2 (17,813), Δg=3 (10,928), Δg=4 (7,662), Δg=1 (5,888), Δg=5 (3,078), Δg=6 (1,140), Δg=7 (356), Δg=8 (24)
//
// === CTL Proof Statistics (209,164,681 proved) ===
// Steps:            min = 304, avg = 304.1, max = 400
// States:           min = 1, avg = 21.9, max = 1,024
// Floors:           floor=6 (209,164,681)
// Moduli:           mod=1 (207,921,275), mod=2 (1,129,985), mod=3 (107,078), mod=4 (3,969), mod=6 (2,271), mod=12 (103)

use pebble::enumeration::{run_enumeration_cli, CtlConfig, PipelineConfig, PipelineStage};

fn main() {
    let pipeline = PipelineConfig {
        stages: vec![
            PipelineStage::StaticBacktrack,
            PipelineStage::Simulation { steps: 100 },
            PipelineStage::Cycler { steps: 100 },
            PipelineStage::SeparatedComponents { steps: 100 },
            // PipelineStage::Bouncer { steps: 100 },
            PipelineStage::MultiBouncer { steps: 100 },
            PipelineStage::Ctl(CtlConfig {
                steps: 100,
                moduli: vec![1, 2, 3],
                ..Default::default()
            }),
            PipelineStage::AcceleratedSim { sim_steps: 1_000 },
            PipelineStage::Cycler { steps: 1_000 },
            PipelineStage::SeparatedComponents { steps: 1_000 },
            // PipelineStage::Bouncer { steps: 1_000 },
            PipelineStage::MultiBouncer { steps: 10_000 },
            PipelineStage::AcceleratedSim { sim_steps: 1_000_000 },
            PipelineStage::Ctl(CtlConfig {
                steps: 1_000,
                max_states: 10_000,
                split_thresh: vec![3, 4],
                moduli: vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12],
                ..Default::default()
            }),
        ],
    };

    run_enumeration_cli(11, pipeline);
}
