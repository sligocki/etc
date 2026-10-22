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
