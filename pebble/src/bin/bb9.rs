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
