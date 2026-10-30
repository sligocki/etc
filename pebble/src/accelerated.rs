use crate::deciders::{AcceleratedInfiniteProof, CyclerProof, Decider, StepDeciderOutcome};
use crate::program::Program;
use crate::simulation::{SimOutcome, Simulator, SparseTape, StepResult, MAX_SPARSE_PEBBLES};
use std::collections::HashMap;

/// A contiguous segment of active cells on the tape at coordinate `offset`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Cluster {
    pub offset: i64,
    pub cells: Vec<u8>,
}

impl Cluster {
    /// Return the leftmost active coordinate of this cluster.
    #[inline]
    pub fn min_x(&self) -> i64 {
        self.offset
    }

    /// Return the rightmost active coordinate of this cluster.
    #[inline]
    pub fn max_x(&self) -> i64 {
        self.offset + self.cells.len() as i64 - 1
    }

    /// Total number of pebbles in this cluster.
    #[inline]
    pub fn total_pebbles(&self) -> usize {
        self.cells.iter().map(|&k| k as usize).sum()
    }
}

/// Periodicity and spatial displacement metrics for an isolated glider or stationary cluster.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GliderInfo {
    /// Period $P \ge 1$ of the glider cycle.
    pub period: u32,
    /// Spatial displacement $\Delta x$ over one period $P$.
    pub dx: i64,
    /// Whether this cluster is strictly quiescent (zero pebble movement: `rule.left == 0 && rule.right == 0`).
    pub is_quiescent: bool,
    /// Trajectory phases: `(relative_offset, cells)` for each phase $0 \le \phi < P$.
    pub phases: Vec<(i64, Vec<u8>)>,
}

impl GliderInfo {
    /// Average velocity $v = \Delta x / P$.
    #[inline]
    pub fn velocity(&self) -> f64 {
        self.dx as f64 / self.period as f64
    }

    /// Returns `true` if this cluster is strictly quiescent ($P = 1, \Delta x = 0$, and no pebbles move).
    #[inline]
    pub fn is_quiescent(&self) -> bool {
        self.is_quiescent
    }

    /// Returns `true` if this cluster has stationary shape ($P = 1, \Delta x = 0$).
    /// Note: if `!is_quiescent`, it is an active dynamic equilibrium cycler!
    #[inline]
    pub fn is_stationary_shape(&self) -> bool {
        self.period == 1 && self.dx == 0
    }

    /// Leftmost relative coordinate at phase `phi`.
    #[inline]
    pub fn relative_min_x(&self, phi: usize) -> i64 {
        self.phases[phi].0
    }

    /// Rightmost relative coordinate at phase `phi`.
    #[inline]
    pub fn relative_max_x(&self, phi: usize) -> i64 {
        self.phases[phi].0 + self.phases[phi].1.len() as i64 - 1
    }
}

/// Memoized cache of glider classifications indexed by normalized cell patterns.
#[derive(Debug, Clone, Default)]
pub struct GliderCache {
    cache: HashMap<Vec<u8>, Option<GliderInfo>>,
}

impl GliderCache {
    /// Create a new empty glider cache.
    pub fn new() -> Self {
        Self {
            cache: HashMap::new(),
        }
    }

    /// Clear all cached classifications.
    pub fn clear(&mut self) {
        self.cache.clear();
    }

    /// Query or test whether `cells` forms a periodic glider under `program`.
    pub fn get_or_evaluate(
        &mut self,
        program: &Program,
        cells: &[u8],
        max_period: u32,
    ) -> Option<GliderInfo> {
        if let Some(cached) = self.cache.get(cells) {
            return cached.clone();
        }

        let info = evaluate_glider(program, cells, max_period);
        self.cache.insert(cells.to_vec(), info.clone());
        info
    }
}

/// Evaluate an isolated cluster in empty space up to `max_period` steps.
fn evaluate_glider(program: &Program, cells: &[u8], max_period: u32) -> Option<GliderInfo> {
    let entries: Vec<(i64, u8)> = cells
        .iter()
        .enumerate()
        .filter(|(_, &k)| k > 0)
        .map(|(i, &k)| (i as i64, k))
        .collect();

    if entries.is_empty() {
        return None;
    }

    let mut sim = Simulator::from_entries(&entries);
    let base_off = sim.offset();
    let mut history: Vec<(i64, Vec<u8>)> = Vec::new();
    history.push((base_off, sim.cells()));

    for step in 1..=max_period {
        match sim.step(program) {
            StepResult::Halted => {
                if step == 1 {
                    // Strictly quiescent (period 1, dx = 0, no pebbles move)
                    return Some(GliderInfo {
                        period: 1,
                        dx: 0,
                        is_quiescent: true,
                        phases: vec![(0, cells.to_vec())],
                    });
                } else {
                    // Stabilized after active transitions; not a periodic cycle at step 0
                    return None;
                }
            }
            StepResult::MissingRule(_) => return None,
            StepResult::Stepped => {
                let cur_cells = sim.cells();
                let cur_off = sim.offset();
                if cur_cells == history[0].1 {
                    let period = step;
                    let dx = cur_off - history[0].0;
                    let phases = history
                        .into_iter()
                        .map(|(off, c)| (off - base_off, c))
                        .collect();
                    return Some(GliderInfo {
                        period,
                        dx,
                        is_quiescent: false, // StepResult::Stepped occurred: pebbles moved!
                        phases,
                    });
                }
                history.push((cur_off, cur_cells));
            }
        }
    }

    None
}

/// Extract clusters of non-zero cells from sparse entries separated by at least `split_threshold` zeros.
pub fn extract_clusters(entries: &[(i64, u8)], split_threshold: usize) -> Vec<Cluster> {
    if entries.is_empty() {
        return Vec::new();
    }
    let split_threshold = split_threshold.max(1) as i64;
    let mut clusters = Vec::new();
    let mut start_idx = 0;

    for i in 0..entries.len() {
        let is_last = i + 1 == entries.len();
        let split_next = if is_last {
            false
        } else {
            match entries[i + 1].0.checked_sub(entries[i].0) {
                Some(diff) => (diff - 1) >= split_threshold,
                None => true,
            }
        };

        if is_last || split_next {
            let start_x = entries[start_idx].0;
            let end_x = entries[i].0;
            let width = match end_x.checked_sub(start_x) {
                Some(diff) => (diff as usize).saturating_add(1),
                None => usize::MAX,
            };
            // A valid cluster in Pebble Automata has at most MAX_SPARSE_PEBBLES non-zero cells.
            // With split_threshold zeros between them, width cannot exceed MAX_SPARSE_PEBBLES * (split_threshold + 2).
            let max_allowed_width = (MAX_SPARSE_PEBBLES * (split_threshold as usize + 2)).max(128);
            if width > max_allowed_width {
                start_idx = i + 1;
                continue;
            }
            let mut cells = vec![0u8; width];
            for &(x, k) in &entries[start_idx..=i] {
                let idx = (x - start_x) as usize;
                if idx < width {
                    cells[idx] = k;
                }
            }
            clusters.push(Cluster {
                offset: start_x,
                cells,
            });
            start_idx = i + 1;
        }
    }

    clusters
}

/// Extract clusters of non-zero cells from a dense slice separated by at least `split_threshold` zeros.
pub fn extract_clusters_dense(offset: i64, cells: &[u8], split_threshold: usize) -> Vec<Cluster> {
    let split_threshold = split_threshold.max(1);
    let mut clusters = Vec::new();
    let mut i = 0;
    while i < cells.len() {
        if cells[i] > 0 {
            let start = i;
            while i + 1 < cells.len() {
                if cells[i + 1] == 0 {
                    let z_start = i + 1;
                    let mut z_end = z_start;
                    while z_end < cells.len() && cells[z_end] == 0 {
                        z_end += 1;
                    }
                    if z_end < cells.len() && (z_end - z_start) < split_threshold {
                        i = z_end;
                    } else {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
            let end = i;
            clusters.push(Cluster {
                offset: offset + start as i64,
                cells: cells[start..=end].to_vec(),
            });
        }
        i += 1;
    }
    clusters
}

/// Greatest common divisor.
fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Least common multiple.
fn lcm(a: u32, b: u32) -> u32 {
    if a == 0 || b == 0 {
        0
    } else {
        (a / gcd(a, b)) * b
    }
}

/// Calculate the number of steps until two adjacent isolated clusters first reach distance `<= d_collide`.
/// Returns `None` if the clusters are diverging or stationary and will never collide.
pub fn collision_time(
    c_left: &Cluster,
    g_left: &GliderInfo,
    c_right: &Cluster,
    g_right: &GliderInfo,
    d_collide: i64,
) -> Option<u64> {
    // Fast path: Period-1 gliders (e.g. single cells or rigid patterns)
    if g_left.period == 1 && g_right.period == 1 {
        let v_l = g_left.dx;
        let v_r = g_right.dx;
        let x_l_max = c_left.max_x();
        let x_r_min = c_right.min_x();
        let dist = x_r_min.checked_sub(x_l_max)?;
        let v_rel = v_l - v_r;
        if v_rel <= 0 {
            return None;
        }
        if dist <= d_collide {
            return Some(0);
        }
        let steps = (dist - d_collide) / v_rel;
        return Some(steps as u64);
    }

    // General path: Multi-period gliders
    let p_l = g_left.period;
    let p_r = g_right.period;
    let super_p = lcm(p_l, p_r) as u64;
    let dx_l_super = (g_left.dx as i128) * (super_p as i128 / p_l as i128);
    let dx_r_super = (g_right.dx as i128) * (super_p as i128 / p_r as i128);
    let v_rel_super = dx_l_super - dx_r_super;

    // Check if diverging over the super period
    if v_rel_super <= 0 {
        // Verify they don't collide during the first cycle
        for t in 0..super_p {
            let phi_l = (t % p_l as u64) as usize;
            let k_l = (t / p_l as u64) as i128;
            let cur_max_l = (c_left.offset as i128)
                + k_l * (g_left.dx as i128)
                + (g_left.relative_max_x(phi_l) as i128);

            let phi_r = (t % p_r as u64) as usize;
            let k_r = (t / p_r as u64) as i128;
            let cur_min_r = (c_right.offset as i128)
                + k_r * (g_right.dx as i128)
                + (g_right.relative_min_x(phi_r) as i128);

            if cur_min_r - cur_max_l <= d_collide as i128 {
                return Some(t);
            }
        }
        return None;
    }

    // Converging multi-period gliders: compute approximate period leap
    let x_l_max = c_left.max_x() as i128;
    let x_r_min = c_right.min_x() as i128;
    let dist = x_r_min - x_l_max;

    let margin = (4 * d_collide) as i128;
    let mut t_base = 0u64;
    if dist > margin {
        let skip_periods = ((dist - margin) / v_rel_super).max(0) as u128;
        let t_base_128 = skip_periods * (super_p as u128);
        if t_base_128 > (u64::MAX / 2) as u128 {
            return None;
        }
        t_base = t_base_128 as u64;
    }

    // Scan forward from t_base to locate exact first collision step
    let mut t = t_base;
    let max_scan = t_base.saturating_add(4 * super_p);
    while t < max_scan {
        let phi_l = (t % p_l as u64) as usize;
        let k_l = (t / p_l as u64) as i128;
        let cur_max_l = (c_left.offset as i128)
            + k_l * (g_left.dx as i128)
            + (g_left.relative_max_x(phi_l) as i128);

        let phi_r = (t % p_r as u64) as usize;
        let k_r = (t / p_r as u64) as i128;
        let cur_min_r = (c_right.offset as i128)
            + k_r * (g_right.dx as i128)
            + (g_right.relative_min_x(phi_r) as i128);

        if cur_min_r - cur_max_l <= d_collide as i128 {
            return Some(t);
        }
        t += 1;
    }

    Some(t)
}

/// Metrics and statistics collected during accelerated simulation.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AcceleratedStats {
    /// Number of fast-forward multi-step leaps performed.
    pub fast_forwards: u64,
    /// Total number of generations skipped via fast-forwarding.
    pub steps_fast_forwarded: u64,
    /// Number of conventional single-step transitions evaluated.
    pub normal_steps: u64,
}

impl AcceleratedStats {
    /// Number of simulation cycles / decisions evaluated (`normal_steps + fast_forwards`).
    #[inline]
    pub fn sim_steps(&self) -> u64 {
        self.normal_steps + self.fast_forwards
    }

    /// Total virtual generations simulated.
    #[inline]
    pub fn total_steps(&self) -> u64 {
        self.steps_fast_forwarded + self.normal_steps
    }
}

/// Result of attempting a fast-forward leap in the accelerated simulator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FastForwardResult {
    /// Advanced simulation time by `steps` generations.
    Jumped(u64),
    /// Simulation halted because all cells on the tape are strictly quiescent (zero movement).
    Halted,
    /// Simulation is infinite because separated non-colliding components are cycling/gliding.
    Inf(Decider),
    /// Cannot fast-forward; normal simulation step required.
    None,
}

/// An accelerated simulator for 1D Pebble Automata that detects separated gliders
/// and fast-forwards collision-free intervals.
pub struct AcceleratedSimulator {
    sim: Simulator,
    total_steps: u64,
    cache: GliderCache,
    stats: AcceleratedStats,
    d_collide: i64,
    split_threshold: usize,
    max_period: u32,
}

impl AcceleratedSimulator {
    /// Create a new accelerated simulator initialized with `initial_pebbles` at coordinate 0.
    pub fn new(initial_pebbles: usize) -> Self {
        Self {
            sim: Simulator::new(initial_pebbles),
            total_steps: 0,
            cache: GliderCache::new(),
            stats: AcceleratedStats::default(),
            d_collide: 2,
            split_threshold: 1,
            max_period: 32,
        }
    }

    /// Create an accelerated simulator from an existing sparse tape.
    pub fn from_tape(tape: SparseTape) -> Self {
        Self {
            sim: Simulator::from_tape(tape),
            total_steps: 0,
            cache: GliderCache::new(),
            stats: AcceleratedStats::default(),
            d_collide: 2,
            split_threshold: 1,
            max_period: 32,
        }
    }

    /// Create an accelerated simulator directly from `(x, pebbles)` coordinate entries.
    pub fn from_entries(entries: &[(i64, u8)]) -> Self {
        Self {
            sim: Simulator::from_entries(entries),
            total_steps: 0,
            cache: GliderCache::new(),
            stats: AcceleratedStats::default(),
            d_collide: 2,
            split_threshold: 1,
            max_period: 32,
        }
    }

    /// Total generations elapsed.
    #[inline]
    pub fn steps(&self) -> u64 {
        self.total_steps
    }

    /// Set explicit generation step offset.
    pub fn with_steps(mut self, steps: u64) -> Self {
        self.total_steps = steps;
        self
    }

    /// Number of simulation cycles / decisions evaluated (`normal_steps + fast_forwards`).
    #[inline]
    pub fn sim_steps(&self) -> u64 {
        self.stats.sim_steps()
    }

    /// Convert back into a standard `Simulator` with the current tape and step count.
    pub fn into_simulator(self) -> Simulator {
        Simulator::from_tape_with_steps(*self.tape(), self.total_steps)
    }

    /// Accelerated simulation performance counters.
    #[inline]
    pub fn stats(&self) -> AcceleratedStats {
        self.stats
    }

    /// Active sparse tape reference.
    #[inline]
    pub fn tape(&self) -> &SparseTape {
        self.sim.tape()
    }

    /// Sparse `(coordinate, pebbles)` entries.
    #[inline]
    pub fn sparse_entries(&self) -> &[(i64, u8)] {
        self.sim.sparse_entries()
    }

    /// Current coordinate offset.
    #[inline]
    pub fn offset(&self) -> i64 {
        self.sim.offset()
    }

    /// Minimum non-zero coordinate.
    #[inline]
    pub fn min_x(&self) -> i64 {
        self.sim.min_x()
    }

    /// Maximum non-zero coordinate.
    #[inline]
    pub fn max_x(&self) -> i64 {
        self.sim.max_x()
    }

    /// Dense cell slice over `[min_x..=max_x]`.
    #[inline]
    pub fn cells(&self) -> Vec<u8> {
        self.sim.cells()
    }

    /// Configure the collision threshold margin (default: 2).
    pub fn with_collision_margin(mut self, margin: i64) -> Self {
        self.d_collide = margin.max(1);
        self
    }

    /// Configure the zero gap threshold for splitting clusters (default: 1).
    pub fn with_split_threshold(mut self, threshold: usize) -> Self {
        self.split_threshold = threshold.max(1);
        self
    }

    /// Attempt to fast-forward the simulation up to `max_steps_jump`.
    ///
    /// If all clusters are identified gliders and the earliest collision occurs at $T > 2$,
    /// fast-forwards all clusters by $\min(T, \text{max\_steps\_jump})$ and returns `FastForwardResult::Jumped(jumped_steps)`.
    /// If all clusters are strictly quiescent, returns `FastForwardResult::Halted`.
    /// If separated clusters will never collide and at least one is active, returns `FastForwardResult::Inf(decider)`.
    /// Otherwise returns `FastForwardResult::None`.
    pub fn try_fast_forward(
        &mut self,
        program: &Program,
        max_steps_jump: u64,
    ) -> FastForwardResult {
        let entries = self.sim.sparse_entries();
        let clusters = extract_clusters(entries, self.split_threshold);

        if clusters.is_empty() {
            return FastForwardResult::Halted;
        }

        let mut gliders = Vec::with_capacity(clusters.len());
        for c in &clusters {
            match self.cache.get_or_evaluate(program, &c.cells, self.max_period) {
                Some(g) => gliders.push(g),
                None => return FastForwardResult::None,
            }
        }

        // 1. If ALL clusters on the tape are strictly quiescent, no pebbles move: HALTED!
        if gliders.iter().all(|g| g.is_quiescent) {
            return FastForwardResult::Halted;
        }

        // 2. If there is only 1 cluster and it is periodic:
        if clusters.len() == 1 {
            let g = &gliders[0];
            // Since it is not quiescent (checked above), it has active motion forever!
            let decider = if g.dx == 0 {
                Decider::Cycler(Some(CyclerProof {
                    period: g.period as u64,
                    dx: 0,
                }))
            } else {
                Decider::Cycler(Some(CyclerProof {
                    period: g.period as u64,
                    dx: g.dx,
                }))
            };
            return FastForwardResult::Inf(decider);
        }

        // 3. For multiple clusters, check collisions between adjacent pairs
        let mut min_t: Option<u64> = None;
        let mut any_converging = false;

        for i in 0..clusters.len() - 1 {
            if let Some(t) = collision_time(
                &clusters[i],
                &gliders[i],
                &clusters[i + 1],
                &gliders[i + 1],
                self.d_collide,
            ) {
                any_converging = true;
                min_t = Some(min_t.map_or(t, |m: u64| m.min(t)));
            }
        }

        // 4. If no clusters will ever collide:
        if !any_converging {
            // At least one cluster is active (checked above), and they never collide!
            let all_stationary = gliders.iter().all(|g| g.dx == 0);
            let decider = if all_stationary {
                let mut super_p = 1u32;
                for g in &gliders {
                    super_p = lcm(super_p, g.period);
                }
                Decider::Cycler(Some(CyclerProof {
                    period: super_p as u64,
                    dx: 0,
                }))
            } else {
                let mut super_p = 1u32;
                for g in &gliders {
                    super_p = lcm(super_p, g.period);
                }
                let super_p = super_p as u64;
                let dxs: Vec<i64> = gliders
                    .iter()
                    .map(|g| g.dx * (super_p / g.period as u64) as i64)
                    .collect();
                let periods: Vec<u32> = gliders.iter().map(|g| g.period).collect();
                Decider::AcceleratedInfinite(Some(AcceleratedInfiniteProof::new(
                    super_p,
                    &dxs,
                    &periods,
                )))
            };
            return FastForwardResult::Inf(decider);
        }

        let Some(t_jump) = min_t else {
            return FastForwardResult::None;
        };

        const MAX_SAFE_COORD: i64 = i64::MAX / 2;
        const MIN_SAFE_COORD: i64 = i64::MIN / 2;

        let mut safe_jump = t_jump.min(max_steps_jump);
        // Ensure total_steps does not overflow u64
        safe_jump = safe_jump.min(u64::MAX.saturating_sub(self.total_steps));

        // Limit jump so no cluster exceeds safe coordinate limits
        for (c, g) in clusters.iter().zip(gliders.iter()) {
            if g.dx > 0 {
                let max_offset_gain = (MAX_SAFE_COORD.saturating_sub(c.offset)).max(0) as u128;
                let max_k = max_offset_gain / (g.dx as u128);
                let max_cluster_jump = (max_k * (g.period as u128)).min(u64::MAX as u128) as u64;
                safe_jump = safe_jump.min(max_cluster_jump);
            } else if g.dx < 0 {
                let max_offset_loss = (c.offset.saturating_sub(MIN_SAFE_COORD)).max(0) as u128;
                let max_k = max_offset_loss / ((-g.dx) as u128);
                let max_cluster_jump = (max_k * (g.period as u128)).min(u64::MAX as u128) as u64;
                safe_jump = safe_jump.min(max_cluster_jump);
            }
        }

        if safe_jump <= 2 {
            return FastForwardResult::None;
        }

        // Compute updated entries at t + safe_jump
        let mut new_entries = Vec::with_capacity(MAX_SPARSE_PEBBLES);
        for (c, g) in clusters.iter().zip(gliders.iter()) {
            let p = g.period as usize;
            let phi = (safe_jump as usize) % p;
            let k = (safe_jump as i128) / (p as i128);
            let base_off = (c.offset as i128) + k * (g.dx as i128) + (g.phases[phi].0 as i128);
            if base_off > i64::MAX as i128 || base_off < i64::MIN as i128 {
                return FastForwardResult::None;
            }
            let base_off = base_off as i64;
            for (idx, &val) in g.phases[phi].1.iter().enumerate() {
                if val > 0 {
                    let x = match base_off.checked_add(idx as i64) {
                        Some(coord) => coord,
                        None => return FastForwardResult::None,
                    };
                    new_entries.push((x, val));
                }
            }
        }

        new_entries.sort_unstable_by_key(|&(x, _)| x);
        if new_entries.len() > MAX_SPARSE_PEBBLES {
            return FastForwardResult::None;
        }

        self.sim = Simulator::from_entries(&new_entries);
        self.total_steps += safe_jump;
        self.stats.fast_forwards += 1;
        self.stats.steps_fast_forwarded += safe_jump;

        FastForwardResult::Jumped(safe_jump)
    }

    /// Advance the simulation by 1 generation or fast-forward if gliders are detected.
    pub fn step(&mut self, program: &Program) -> StepResult {
        // Try fast-forwarding if possible
        match self.try_fast_forward(program, 10_000) {
            FastForwardResult::Halted => return StepResult::Halted,
            FastForwardResult::Jumped(_) => return StepResult::Stepped,
            FastForwardResult::Inf(_) | FastForwardResult::None => {}
        }

        // Otherwise advance 1 step with conventional simulator
        let res = self.sim.step(program);
        if res == StepResult::Stepped {
            self.total_steps += 1;
            self.stats.normal_steps += 1;
        }
        res
    }

    /// Run the simulation up to `max_steps` generations.
    pub fn run(&mut self, program: &Program, max_steps: u64) -> SimOutcome {
        const MAX_SAFE_COORD: i64 = i64::MAX / 2;
        const MIN_SAFE_COORD: i64 = i64::MIN / 2;
        while self.total_steps < max_steps {
            if self.min_x() <= MIN_SAFE_COORD
                || self.max_x() >= MAX_SAFE_COORD
                || self.total_steps >= u64::MAX - 100_000
            {
                return SimOutcome::unknown_coord_overflow(self.total_steps);
            }

            let remaining = max_steps - self.total_steps;
            match self.try_fast_forward(program, remaining) {
                FastForwardResult::Halted => {
                    return SimOutcome::Halted {
                        steps: self.total_steps,
                    };
                }
                FastForwardResult::Inf(decider) => {
                    return SimOutcome::Inf {
                        decider,
                        steps: self.total_steps,
                    };
                }
                FastForwardResult::Jumped(_) => {
                    continue;
                }
                FastForwardResult::None => {}
            }

            match self.sim.step(program) {
                StepResult::Stepped => {
                    self.total_steps += 1;
                    self.stats.normal_steps += 1;
                }
                StepResult::Halted => {
                    return SimOutcome::Halted {
                        steps: self.total_steps,
                    };
                }
                StepResult::MissingRule(pebbles) => {
                    return SimOutcome::MissingRule {
                        pebbles,
                        steps: self.total_steps,
                    };
                }
            }
        }

        SimOutcome::unknown_step_limit(self.total_steps)
    }

    /// Run the simulation until `max_sim_steps` simulation steps have been evaluated
    /// (where `sim_steps = normal_steps + fast_forwards`).
    pub fn run_sim_steps(&mut self, program: &Program, max_sim_steps: u64) -> SimOutcome {
        const MAX_SAFE_COORD: i64 = i64::MAX / 2;
        const MIN_SAFE_COORD: i64 = i64::MIN / 2;
        let initial_sim_steps = self.sim_steps();
        while self.sim_steps().saturating_sub(initial_sim_steps) < max_sim_steps {
            if self.min_x() <= MIN_SAFE_COORD
                || self.max_x() >= MAX_SAFE_COORD
                || self.total_steps >= u64::MAX - 100_000
            {
                return SimOutcome::unknown_coord_overflow(self.total_steps);
            }

            match self.try_fast_forward(program, u64::MAX) {
                FastForwardResult::Halted => {
                    return SimOutcome::Halted {
                        steps: self.total_steps,
                    };
                }
                FastForwardResult::Inf(decider) => {
                    return SimOutcome::Inf {
                        decider,
                        steps: self.total_steps,
                    };
                }
                FastForwardResult::Jumped(_) => {
                    continue;
                }
                FastForwardResult::None => {}
            }

            match self.sim.step(program) {
                StepResult::Stepped => {
                    self.total_steps += 1;
                    self.stats.normal_steps += 1;
                }
                StepResult::Halted => {
                    return SimOutcome::Halted {
                        steps: self.total_steps,
                    };
                }
                StepResult::MissingRule(pebbles) => {
                    return SimOutcome::MissingRule {
                        pebbles,
                        steps: self.total_steps,
                    };
                }
            }
        }

        SimOutcome::unknown_step_limit(self.total_steps)
    }
}

/// Decider interface: Run accelerated simulation from an existing `sim` state up to `max_sim_steps`
/// simulation steps (`normal_steps + fast_forwards`).
pub fn decide_accelerated_sim_from_sim(
    program: &Program,
    sim: &mut Simulator,
    max_sim_steps: u64,
) -> StepDeciderOutcome {
    let mut acc = AcceleratedSimulator::from_tape(*sim.tape()).with_steps(sim.steps());
    let outcome = acc.run_sim_steps(program, max_sim_steps);
    *sim = acc.into_simulator();
    match outcome {
        SimOutcome::Halted { steps } => StepDeciderOutcome::Halted { steps },
        SimOutcome::Inf { decider, .. } => StepDeciderOutcome::Proved(decider),
        SimOutcome::MissingRule { pebbles, steps } => {
            StepDeciderOutcome::MissingRule { pebbles, steps }
        }
        SimOutcome::Unknown { .. } => StepDeciderOutcome::Undecided,
    }
}

/// Decider interface: Run accelerated simulation on `program` up to `max_sim_steps` simulation steps.
pub fn decide_accelerated_sim(program: &Program, max_sim_steps: u64) -> StepDeciderOutcome {
    let mut sim = Simulator::new(program.size());
    decide_accelerated_sim_from_sim(program, &mut sim, max_sim_steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prog1_exact_equivalence() {
        let prog: Program = "00_00_00_04_41_11_33_80_22_12_56".parse().unwrap();
        let target = 20_000u64;

        let mut std_sim = Simulator::new(prog.size());
        for _ in 0..target {
            if std_sim.step(&prog) != StepResult::Stepped {
                break;
            }
        }

        let mut acc_sim = AcceleratedSimulator::new(prog.size());
        let outcome = acc_sim.run(&prog, target);

        assert_eq!(outcome.steps(), target);
        assert_eq!(acc_sim.steps(), std_sim.steps());
        assert_eq!(acc_sim.sparse_entries(), std_sim.sparse_entries());
        assert!(acc_sim.stats().fast_forwards > 0);
        assert!(acc_sim.stats().steps_fast_forwarded > 0);
    }

    #[test]
    fn test_prog2_exact_equivalence() {
        let prog: Program = "00_00_00_40_10_00_00_08_41_11_00_a1".parse().unwrap();
        let target = 20_000u64;

        let mut std_sim = Simulator::new(prog.size());
        for _ in 0..target {
            if std_sim.step(&prog) != StepResult::Stepped {
                break;
            }
        }

        let mut acc_sim = AcceleratedSimulator::new(prog.size());
        let outcome = acc_sim.run(&prog, target);

        assert_eq!(outcome.steps(), target);
        assert_eq!(acc_sim.steps(), std_sim.steps());
        assert_eq!(acc_sim.sparse_entries(), std_sim.sparse_entries());
        assert!(acc_sim.stats().fast_forwards > 0);
        assert!(acc_sim.stats().steps_fast_forwarded > 0);
    }

    #[test]
    fn test_glider_classification() {
        let prog: Program = "00_00_00_04_41_11_33_80_22_12_56".parse().unwrap();
        let mut cache = GliderCache::new();

        // 1 is stationary and quiescent
        let g1 = cache.get_or_evaluate(&prog, &[1], 16).unwrap();
        assert_eq!(g1.period, 1);
        assert_eq!(g1.dx, 0);
        assert!(g1.is_quiescent);

        // 4 moves right by 1
        let g4 = cache.get_or_evaluate(&prog, &[4], 16).unwrap();
        assert_eq!(g4.period, 1);
        assert_eq!(g4.dx, 1);
        assert!(!g4.is_quiescent);

        // 8 moves left by 1
        let g8 = cache.get_or_evaluate(&prog, &[8], 16).unwrap();
        assert_eq!(g8.period, 1);
        assert_eq!(g8.dx, -1);
        assert!(!g8.is_quiescent);
    }

    #[test]
    fn test_dynamic_equilibrium_is_cycler_not_halted() {
        // 2 -> 0|1|1, 3 -> 1|2|0
        // [2, 3] shuttles pebbles in dynamic equilibrium (period 1, dx = 0).
        let prog: Program = "00_01_10".parse().unwrap();
        let mut acc_sim = AcceleratedSimulator::from_entries(&[(0, 2), (1, 3)]);
        let outcome = acc_sim.run(&prog, 100);
        assert_eq!(
            outcome,
            SimOutcome::Inf {
                decider: Decider::Cycler(Some(CyclerProof { period: 1, dx: 0 })),
                steps: 0,
            }
        );

        // Also test with another separated quiescent cluster: must still be Inf, not Halted!
        let mut acc_sim2 = AcceleratedSimulator::from_entries(&[(0, 2), (1, 3), (10, 1)]);
        let outcome2 = acc_sim2.run(&prog, 100);
        assert_eq!(
            outcome2,
            SimOutcome::Inf {
                decider: Decider::Cycler(Some(CyclerProof { period: 1, dx: 0 })),
                steps: 0,
            }
        );
    }

    #[test]
    fn test_prog1_halting_equivalence() {
        let prog: Program = "00_00_00_04_41_11_33_80_22_12_56".parse().unwrap();
        let mut acc_sim = AcceleratedSimulator::new(prog.size());
        let outcome = acc_sim.run(&prog, 30_000_000);
        assert_eq!(outcome, SimOutcome::Halted { steps: 25_024_260 });
        assert_eq!(acc_sim.steps(), 25_024_260);
        assert_eq!(
            acc_sim.sparse_entries(),
            &[(-4004, 3), (-4003, 1), (-4002, 3), (-4001, 3), (3026, 1)]
        );
    }

    #[test]
    fn test_exponential_glider_safety_bounds() {
        // Program with exponential collision doubling (reaches > 10^18 generations)
        let prog: Program = "00_02_01_40_13_41_00_17_13_28_01".parse().unwrap();
        let mut acc_sim = AcceleratedSimulator::new(prog.size());
        let outcome = acc_sim.run_sim_steps(&prog, 5000);
        // Must safely terminate as Unknown without panicking or capacity overflow
        assert!(outcome.is_unknown());
        assert!(acc_sim.steps() > 1_000_000_000_000_000);
    }

    #[test]
    fn test_diverging_gliders_accelerated_infinite() {
        let prog: Program = "00_00_00_04_41_11_33_80_22_12_56".parse().unwrap();
        // Pebble 8 moves left (dx = -1), Pebble 4 moves right (dx = 1)
        let mut acc_sim = AcceleratedSimulator::from_entries(&[(-10, 8), (10, 4)]);
        let outcome = acc_sim.run(&prog, 100);
        assert_eq!(
            outcome,
            SimOutcome::Inf {
                decider: Decider::AcceleratedInfinite(Some(AcceleratedInfiniteProof::new(
                    1,
                    &[-1, 1],
                    &[1, 1],
                ))),
                steps: 0,
            }
        );
    }
}
