import { TuringMachine, Simulator } from './simulator.js';
import { Renderer } from './renderer.js';

let simulator = null;
let renderer = null;
let playInterval = null;

const input = document.getElementById('tm-input');
const btnLoad = document.getElementById('btn-load');
const btnPlay = document.getElementById('btn-play');
const btnStart = document.getElementById('btn-start');
const btnEnd = document.getElementById('btn-end');
const btnBack = document.getElementById('btn-back');
const btnForward = document.getElementById('btn-forward');
const speedSlider = document.getElementById('speed-slider');

const statState = document.getElementById('stat-state');
const statSteps = document.getElementById('stat-steps');

function updateUI() {
    statState.textContent = simulator.getStateChar();
    statSteps.textContent = simulator.currentStep;
    
    if (simulator.state === 'Z' && simulator.currentStep === simulator.steps) {
        btnForward.disabled = true;
        btnEnd.disabled = true;
        stopPlay();
        statState.style.color = '#ef4444';
    } else {
        btnForward.disabled = false;
        btnEnd.disabled = false;
        statState.style.color = '#38bdf8';
    }
    
    btnBack.disabled = simulator.currentStep === 0;
    btnStart.disabled = simulator.currentStep === 0;
    
    renderer.update(simulator);
}

function loadTM() {
    try {
        const tmStr = input.value.trim();
        const tm = new TuringMachine(tmStr);
        simulator = new Simulator(tm);
        
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
        updateUI();
    }
}

function stepBackward() {
    if (!simulator) return;
    if (simulator.stepBackward()) {
        updateUI();
    }
}

function jumpToStart() {
    if (!simulator) return;
    if (simulator.jumpToStart()) {
        updateUI();
    }
}

function jumpToEnd() {
    if (!simulator) return;
    if (simulator.jumpToEnd()) {
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
    if (simulator.state === 'Z' && simulator.currentStep === simulator.steps) return;
    btnPlay.textContent = '⏸ Pause';
    let delay = parseInt(speedSlider.max) - parseInt(speedSlider.value) + parseInt(speedSlider.min);
    
    playInterval = setInterval(() => {
        if (!simulator.stepForward()) {
            stopPlay();
        }
        updateUI();
    }, delay);
}

function stopPlay() {
    if (playInterval) {
        clearInterval(playInterval);
        playInterval = null;
    }
    btnPlay.textContent = '▶ Play';
}

speedSlider.addEventListener('input', () => {
    if (playInterval) {
        stopPlay();
        startPlay();
    }
});

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
btnStart.addEventListener('click', jumpToStart);
btnEnd.addEventListener('click', jumpToEnd);
btnPlay.addEventListener('click', togglePlay);

loadTM();
