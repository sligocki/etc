import * as d3 from 'd3';

const COLORS = {
    'R': '#ff4d4d', // Red
    'G': '#4dff4d', // Green
    'B': '#4d4dff'  // Blue
};

export class Renderer {
    constructor(svgSelector) {
        this.svg = d3.select(svgSelector);
        this.width = this.svg.node().getBoundingClientRect().width;
        this.height = this.svg.node().getBoundingClientRect().height;
        
        this.g = this.svg.append("g");
        
        this.svg.call(d3.zoom().scaleExtent([0.1, 10]).on("zoom", (event) => {
            this.g.attr("transform", event.transform);
        }));
        
        this.simulation = d3.forceSimulation()
            .force("link", d3.forceLink().id(d => d.id).distance(60))
            .force("charge", d3.forceManyBody().strength(-300))
            .force("center", d3.forceCenter(this.width / 2, this.height / 2));
            
        this.nodesData = [];
        this.linksData = [];
        this.nodeMap = new Map();
        
        this.linkGroup = this.g.append("g").attr("class", "links");
        this.nodeGroup = this.g.append("g").attr("class", "nodes");
    }
    
    update(simulator) {
        // Build the set of visited paths from simulator history
        let visitedPaths = new Set();
        for (let state of simulator.history) {
            visitedPaths.add(state.head.join(','));
        }
        
        // Add current head if not present
        visitedPaths.add(simulator.head.join(','));
        
        let newNodes = [];
        let newLinks = [];
        
        // Ensure all visited paths are in the graph
        visitedPaths.forEach(pathStr => {
            if (!this.nodeMap.has(pathStr)) {
                let node = { id: pathStr };
                
                // If it's not the root, add a link to its parent and inherit coordinates
                if (pathStr !== "") {
                    let parts = pathStr.split(',');
                    let dir = parts.pop();
                    let parentPath = parts.join(',');
                    
                    let parentNode = this.nodeMap.get(parentPath);
                    if (parentNode) {
                        node.x = parentNode.x;
                        node.y = parentNode.y;
                    }
                    
                    this.linksData.push({
                        source: parentPath,
                        target: pathStr,
                        dir: dir
                    });
                } else {
                    node.x = this.width / 2;
                    node.y = this.height / 2;
                }
                
                this.nodeMap.set(pathStr, node);
                this.nodesData.push(node);
            }
        });
        
        // Update nodes with current symbols and head status
        let currentHeadId = simulator.head.join(',');
        for (let node of this.nodesData) {
            node.symbol = simulator.tape[node.id] || 0;
            node.isHead = (node.id === currentHeadId);
        }
        
        this.render();
    }
    
    render() {
        // Links
        let link = this.linkGroup.selectAll("line")
            .data(this.linksData, d => d.source.id + "-" + d.target.id);
            
        let linkEnter = link.enter().append("line")
            .attr("stroke-width", 4)
            .attr("stroke", d => COLORS[d.dir]);
            
        link = linkEnter.merge(link);
        
        // Nodes
        let node = this.nodeGroup.selectAll("g.node")
            .data(this.nodesData, d => d.id);
            
        let nodeEnter = node.enter().append("g")
            .attr("class", "node")
            .call(d3.drag()
                .on("start", (event, d) => {
                    if (!event.active) this.simulation.alphaTarget(0.3).restart();
                    d.fx = d.x;
                    d.fy = d.y;
                })
                .on("drag", (event, d) => {
                    d.fx = event.x;
                    d.fy = event.y;
                })
                .on("end", (event, d) => {
                    if (!event.active) this.simulation.alphaTarget(0);
                    d.fx = null;
                    d.fy = null;
                }));
                
        nodeEnter.append("circle")
            .attr("r", 15);
            
        nodeEnter.append("text")
            .attr("dy", 5)
            .attr("text-anchor", "middle")
            .attr("fill", "white")
            .attr("font-family", "Inter, sans-serif")
            .attr("font-weight", "bold");
            
        node = nodeEnter.merge(node);
        
        // Update visual states dynamically
        node.select("circle")
            .attr("fill", d => d.symbol === 1 ? "#fff" : "#333")
            .attr("stroke", d => d.isHead ? "#ffcc00" : "#555")
            .attr("stroke-width", d => d.isHead ? 4 : 2);
            
        node.select("text")
            .text(d => d.symbol)
            .attr("fill", d => d.symbol === 1 ? "#000" : "#fff");
        
        this.simulation.nodes(this.nodesData).on("tick", () => {
            link
                .attr("x1", d => d.source.x)
                .attr("y1", d => d.source.y)
                .attr("x2", d => d.target.x)
                .attr("y2", d => d.target.y);
                
            node
                .attr("transform", d => `translate(${d.x},${d.y})`);
        });
        
        this.simulation.force("link").links(this.linksData);
        this.simulation.alpha(0.05).restart();
    }
}
