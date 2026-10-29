// === Final Statistics (peBBle(9), max_steps = 100000) ===
// Total programs:         528,594,612
// Halted programs:        93,824,392 (17.75%)
// Infinite programs:      434,770,220 (82.25%)
// Unknown programs:       0 (0.00%)
// Max halting step count: 63,577
// Champion program:       00_20_10_04_41_21_00_25_18
// Wallclock runtime:      116.046s
// Throughput:             4,555,031 programs/s
//
// === Pipeline & Decider Performance ===
// Stage / Decider                         Run On     Split On       Halted          Inf     Total Time     Avg / Prog
// -------------------------------------------------------------------------------------------------------------------
// StaticBacktrack                    568,498,400            0            0  140,745,964        30.47 s          53 ns
// Simulation (100 steps)             427,752,436   39,903,746   93,824,350  260,543,913      1248.92 s        2.92 µs
// Cycler (100 steps)                  33,480,427           13           13   23,039,829       242.21 s        7.23 µs
// SeparatedComponents (100 steps)     10,440,572            2            2   10,232,435        44.05 s        4.22 µs
// CTL (100 steps, moduli=[1, 2, 3])      208,133            7            7      208,079         4.01 s       19.24 µs
// Simulation (100000 steps)                   40           20           20            0       13.51 ms      337.79 µs
// -------------------------------------------------------------------------------------------------------------------
//
// === Halting Step Distribution (93,824,392 halted) ===
// Steps:            min = 0, avg = 13.5, max = 63,577
//
// Step Range               k                 Count   Pct Halted  Distribution
// ----------------------------------------------------------------------------------------
// 0                        -                     1        0.00%
// [1, 2)                   k=0                  28        0.00%
// [2, 4)                   k=1              50,234        0.05%
// [4, 8)                   k=2          11,857,177       12.64%  ███
// [8, 16)                  k=3          50,745,718       54.09%  ██████████████
// [16, 32)                 k=4          31,013,138       33.05%  ████████
// [32, 64)                 k=5             157,803        0.17%
// [64, 128)                k=6                 255        0.00%
// [128, 256)               k=7                   9        0.00%
// [256, 512)               k=8                  10        0.00%
// [512, 1,024)             k=9                   2        0.00%
// [1,024, 2,048)           k=10                  1        0.00%
// [2,048, 4,096)           k=11                  0        0.00%
// [4,096, 8,192)           k=12                  9        0.00%
// [8,192, 16,384)          k=13                  6        0.00%
// [16,384, 32,768)         k=14                  0        0.00%
// [32,768, 65,536)         k=15                  1        0.00%
// ----------------------------------------------------------------------------------------
//
// === Cycler Proof Statistics (23,039,829 proved) ===
// Periods:          min = 1, avg = 3.8, max = 91
// Top periods:      p=2 (8,363,071), p=1 (4,152,574), p=3 (2,253,194), p=4 (2,012,836)
// Displacements:    dx=0 (14,772,039), dx=1 (2,969,888), dx=-1 (2,541,642)
//
// === SeparatedComponents Proof Statistics (10,232,435 proved) ===
// Periods:          min = 1, avg = 3.5, max = 56
// Top periods:      p=2 (3,936,337), p=3 (3,141,959), p=4 (1,097,560), p=5 (631,265)
//
// === CTL Proof Statistics (208,079 proved) ===
// Steps:            min = 304, avg = 304.0, max = 308
// States:           min = 1, avg = 12.2, max = 645
// Floors:           floor=6 (208,079)
// Moduli:           mod=1 (207,948), mod=2 (108), mod=3 (23)

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
                moduli: vec![1, 2, 3],
                ..Default::default()
            }),
            PipelineStage::Simulation { steps: 100_000 },
        ],
    };

    run_enumeration_cli(9, pipeline);
}
