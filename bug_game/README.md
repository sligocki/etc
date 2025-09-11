Bug Game: https://buglab.ru/index.asp?main=game

Create a maze that takes a bug as long as possible to escape.

Shared by @savask on Busy Beaver Discord:

> The labyrinth is a rectangular square N x M grid. Each grid cell can either be empty or contain a wall (or contain a bug), we also assume that the outer border of the rectangle is filled with walls. The bug starts on the top left corner facing up, and it must reach the bottom right corner. The bug can face one of four directions and it moves one cell per simulation step; obviously it can't move through walls. Its pathfinding algorithm is as follows: the bug remembers how many times it visited each cell, and on each step it goes into the least visited cell among bug's immediate neighbors. If there are several such cells, but one of the least visited cells lies right ahead of the bug, then it continues moving in the same direction. In other case, the bug selects the next cell (among least visited) with respect to the following precedence: down, right, up, left.

Example usage:

```bash
python3 bug.py designs/savask_630.txt
##############################
#B..#....#.####.#..#.####.##.#
#.#.##.#..#.#.....#.#.#......#
#...#..#.#.##..##........##.##
#.............#...........#.##
#.#..##.#.#...###..#..#...#..#
#.....#...#..#....#...#.##..F#
##############################
Score: 630
##############################
#+++#8+++#.####2#32#.####.##2#
#+#+##9#+8#.#56534#1#1#111123#
#+++#9+#+#6##74##32313221##1##
#++++++++++879#23322221122#1##
#+#++##+#+#797###21#11#.12#1.#
#++++8#+++#88#1222#.11#.##.1B#
##############################
```