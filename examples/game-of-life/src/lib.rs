#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Grid<const N: usize, const M: usize> {
    cells: [[bool; M]; N],
}

impl<const N: usize, const M: usize> Grid<N, M> {
    pub const fn new(cells: [[bool; M]; N]) -> Self {
        Self { cells }
    }

    pub const fn dead() -> Self {
        Self { cells: [[false; M]; N] }
    }

    pub fn get(&self, i: usize, j: usize) -> bool {
        if i < N && j < M {
            self.cells[i][j]
        } else {
            false
        }
    }

    pub fn set(&mut self, i: usize, j: usize, alive: bool) {
        if i < N && j < M {
            self.cells[i][j] = alive;
        }
    }

    fn count_neighbors(&self, i: usize, j: usize) -> u8 {
        let mut count = 0u8;
        for di in [N - 1, 0, 1] {
            for dj in [M - 1, 0, 1] {
                if di == 0 && dj == 0 {
                    continue;
                }
                let ni = (i + di) % N;
                let nj = (j + dj) % M;
                if self.cells[ni][nj] {
                    count += 1;
                }
            }
        }
        count
    }

    pub fn step(&self) -> Self {
        let mut next = Self::dead();
        for i in 0..N {
            for j in 0..M {
                let neighbors = self.count_neighbors(i, j);
                let alive = self.cells[i][j];
                next.cells[i][j] = matches!(
                    (alive, neighbors),
                    (true, 2) | (true, 3) | (false, 3)
                );
            }
        }
        next
    }

    pub fn step_n(&self, n: usize) -> Self {
        let mut grid = *self;
        for _ in 0..n {
            grid = grid.step();
        }
        grid
    }
}

impl<const N: usize, const M: usize> std::fmt::Display for Grid<N, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for row in &self.cells {
            for &cell in row {
                write!(f, "{}", if cell { '#' } else { '.' })?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

pub fn blinker() -> Grid<5, 5> {
    Grid::new([
        [false, false, false, false, false],
        [false, false, true,  false, false],
        [false, false, true,  false, false],
        [false, false, true,  false, false],
        [false, false, false, false, false],
    ])
}

pub fn blinker_phase2() -> Grid<5, 5> {
    Grid::new([
        [false, false, false, false, false],
        [false, false, false, false, false],
        [false, true,  true,  true,  false],
        [false, false, false, false, false],
        [false, false, false, false, false],
    ])
}

pub fn glider() -> Grid<6, 6> {
    Grid::new([
        [false, true,  false, false, false, false],
        [false, false, true,  false, false, false],
        [true,  true,  true,  false, false, false],
        [false, false, false, false, false, false],
        [false, false, false, false, false, false],
        [false, false, false, false, false, false],
    ])
}

pub fn glider_translated() -> Grid<6, 6> {
    Grid::new([
        [false, false, false, false, false, false],
        [false, false, true,  false, false, false],
        [false, false, false, true,  false, false],
        [false, true,  true,  true,  false, false],
        [false, false, false, false, false, false],
        [false, false, false, false, false, false],
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blinker_has_period_2() {
        let b0 = blinker();
        let b1 = b0.step();
        let b2 = b1.step();
        assert_eq!(b1, blinker_phase2());
        assert_eq!(b2, b0);
    }

    #[test]
    fn glider_translates_after_4_steps() {
        let g0 = glider();
        let g4 = g0.step_n(4);
        assert_eq!(g4, glider_translated());
    }

    #[test]
    fn block_is_stable() {
        let block: Grid<4, 4> = Grid::new([
            [false, false, false, false],
            [false, true,  true,  false],
            [false, true,  true,  false],
            [false, false, false, false],
        ]);
        assert_eq!(block.step(), block);
    }
}
