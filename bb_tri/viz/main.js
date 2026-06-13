import { TuringMachine, Simulator } from './simulator.js';
import { Renderer } from './renderer.js';

let simulator = null;
let renderer = null;
let playInterval = null;

const input = document.getElementById('tm-input');
const btnLoad = document.getElementById('btn-load');
const btnPlay = document.getElementById('btn-play');
const btnReset = document.getElementById('btn-reset');
const btnBack = document.getElementById('btn-back');
const btnForward = document.getElementById('btn-forward');

const statState = document.getElementById('stat-state');
const statSteps = document.getElementById('stat-steps');

function updateUI() {
    statState.textContent = simulator.getStateChar();
    statSteps.textContent = simulator.steps;
    
    if (simulator.state === 'Z') {
        btnForward.disabled = true;
        stopPlay();
        statState.style.color = '#ef4444'; // Red for halt
    } else {
        btnForward.disabled = false;
        statState.style.color = '#38bdf8';
    }
    
    btnBack.disabled = simulator.steps === 0;
    
    renderer.update(simulator);
}

function loadTM() {
    try {
        const tmStr = input.value.trim();
        const tm = new TuringMachine(tmStr);
        simulator = new Simulator(tm);
        
        // Clear SVG
        document.getElementById('viz-canvas').innerHTML = '';
        renderer = new Renderer('#viz-canvas');
        
        updateUI();
    } catch (e) {
        alert("Failed to load TM: " + e.message);
    }
}

function stepForward() {
    if (!simulator) return;
    if (simulator.stepForward()) {
        updateUI();
    } else {
        updateUI(); // To show Halt
    }
}

function stepBackward() {
    if (!simulator) return;
    if (simulator.stepBackward()) {
        updateUI();
    }
}

function togglePlay() {
    if (playInterval) {
        stopPlay();
    } else {
        startPlay();
    }
}

function startPlay() {
    if (simulator.state === 'Z') return;
    btnPlay.textContent = '⏸ Pause';
    playInterval = setInterval(() => {
        if (!simulator.stepForward()) {
            stopPlay();
        }
        updateUI();
    }, 200); // 200ms per step
}

function stopPlay() {
    if (playInterval) {
        clearInterval(playInterval);
        playInterval = null;
    }
    btnPlay.textContent = '▶ Play';
}

btnLoad.addEventListener('click', () => {
    stopPlay();
    loadTM();
});

input.addEventListener('keypress', (e) => {
    if (e.key === 'Enter') {
        stopPlay();
        loadTM();
    }
});

btnForward.addEventListener('click', stepForward);
btnBack.addEventListener('click', stepBackward);
btnPlay.addEventListener('click', togglePlay);
btnReset.addEventListener('click', () => {
    stopPlay();
    loadTM();
});

// Initial load
loadTM();
