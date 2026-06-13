export class TuringMachine {
    constructor(tmString) {
        this.tmString = tmString;
        this.states = [];
        this.numSymbols = 0;
        this.parse(tmString);
    }
    
    parse(s) {
        const statesStr = s.split('_');
        if (statesStr.length === 0) throw new Error("Empty TM");
        this.numSymbols = statesStr[0].length / 3;
        
        for (let stateStr of statesStr) {
            let trans = [];
            for (let i = 0; i < this.numSymbols; i++) {
                let chunk = stateStr.substring(i * 3, i * 3 + 3);
                if (chunk === "---") {
                    trans.push(null);
                    continue;
                }
                let write = parseInt(chunk[0], 10);
                let dir = chunk[1];
                let next = chunk[2] === 'Z' ? 'Z' : chunk.charCodeAt(2) - 65;
                trans.push({write, dir, next});
            }
            this.states.push(trans);
        }
    }
    
    getTransition(state, symbol) {
        if (state === 'Z') return null;
        if (!this.states[state]) return null;
        return this.states[state][symbol];
    }
}

export class Simulator {
    constructor(tm) {
        this.tm = tm;
        this.tape = {}; // key: path string, val: symbol
        this.head = [];
        this.state = 0;
        this.steps = 0; // synonymous with maxStep
        this.currentStep = 0;
        
        this.history = [];
        this.saveState();
    }
    
    saveState() {
        this.history.push({
            tape: {...this.tape},
            head: [...this.head],
            state: this.state
        });
    }

    restoreState(index) {
        let s = this.history[index];
        this.tape = {...s.tape};
        this.head = [...s.head];
        this.state = s.state;
    }
    
    read() {
        let path = this.head.join(',');
        return this.tape[path] || 0;
    }
    
    write(sym) {
        let path = this.head.join(',');
        if (sym === 0) {
            delete this.tape[path];
        } else {
            this.tape[path] = sym;
        }
    }
    
    stepForward() {
        if (this.currentStep < this.steps) {
            this.currentStep++;
            this.restoreState(this.currentStep);
            return true;
        }

        if (this.state === 'Z') return false;
        
        let sym = this.read();
        let trans = this.tm.getTransition(this.state, sym);
        
        if (!trans) {
            this.state = 'Z';
            this.steps++;
            this.currentStep++;
            this.saveState(); // Record that we halted
            return false;
        }
        
        this.write(trans.write);
        
        if (this.head.length > 0 && this.head[this.head.length - 1] === trans.dir) {
            this.head.pop();
        } else {
            this.head.push(trans.dir);
        }
        
        this.state = trans.next;
        this.steps++;
        this.currentStep++;
        this.saveState();
        return true;
    }
    
    stepBackward() {
        if (this.currentStep > 0) {
            this.currentStep--;
            this.restoreState(this.currentStep);
            return true;
        }
        return false;
    }

    jumpToStart() {
        if (this.currentStep > 0) {
            this.currentStep = 0;
            this.restoreState(0);
            return true;
        }
        return false;
    }

    jumpToEnd() {
        let limit = 10000; // prevent infinite loops in UI
        let advanced = false;
        while (this.state !== 'Z' && this.steps < limit) {
            if (!this.stepForward()) break;
            advanced = true;
        }
        // If we were just scrubbing back, and we jump to end:
        if (this.currentStep < this.steps) {
            this.currentStep = this.steps;
            this.restoreState(this.currentStep);
            advanced = true;
        }
        return advanced;
    }

    getStateChar() {
        return this.state === 'Z' ? 'Z' : String.fromCharCode(65 + this.state);
    }
}
