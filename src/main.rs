use std::collections::HashMap;
use z3::{Config, Context, SatResult, Solver};
use z3::ast::{Ast, Bool, BV};

//   dist(0, 0) -- top(0, 0) -- dist(0, 1) -- top(0, 1) -- dist(0, 2)
//       |                          |                          |
//       |                          |                          |
//   left(0, 0)   cell(0, 0)    left(0, 1)   cell(0, 1)    left(0, 2)
//       |                          |                          |
//       |                          |                          |
//   dist(1, 0) -- top(1, 0) -- dist(1, 1) -- top(1, 1) -- dist(1, 2)
//       |                          |                          |
//       |                          |                          |
//   left(1, 0)   cell(1, 0)    left(1, 1)   cell(1, 1)    left(1, 2)
//       |                          |                          |
//       |                          |                          |
//   dist(2, 0) -- top(2, 0) -- dist(2, 1) -- top(2, 1) -- dist(2, 2)

fn main() {
    let mut args = std::env::args();
    let _ = args.next();
    let Some(width) = args.next() else {
        eprintln!("Usage: ./slitherlink <width> <height> <puzzle>");
        return;
    };
    let width = width.parse().unwrap();
    let Some(height) = args.next() else {
        eprintln!("Usage: ./slitherlink <width> <height> <puzzle>");
        return;
    };
    let height = height.parse().unwrap();
    let Some(puzzle) = args.next() else {
        eprintln!("Usage: ./slitherlink <width> <height> <puzzle>");
        return;
    };
    let mut cells = HashMap::new();
    let mut idx = 0;
    for ch in puzzle.chars() {
        if ('0'..='3').contains(&ch) {
            cells.insert(idx, (ch as u8) - b'0');
        } else {
            idx += (ch as usize) - ('a' as usize);
        }
        idx += 1;
    }

    let config = Config::new();
    let ctx = Context::new(&config);

    let mut top = HashMap::new();
    let mut left = HashMap::new();
    for i in 0..=height {
        for j in 0..=width {
            if i != height {
                left.insert((i, j), Bool::fresh_const(&ctx, ""));
            }
            if j != width {
                top.insert((i, j), Bool::fresh_const(&ctx, ""));
            }
        }
    }
    let solver = Solver::new(&ctx);
    for i in 0..height {
        for j in 0..width {
            if let Some(val) = cells.get(&(width * i + j)) {
                let constraint = Bool::pb_eq(&ctx, &[
                    (&top[&(i, j)], 1),
                    (&left[&(i, j)], 1),
                    (&top[&(i + 1, j)], 1),
                    (&left[&(i, j + 1)], 1),
                ], *val as i32);
                solver.assert(&constraint);
            }
        }
    }
    let mut constraints = Vec::with_capacity(4);
    for i in 0..=height {
        for j in 0..=width {
            if i < height {
                constraints.push((&left[&(i, j)], 1));
            }
            if i > 0 {
                constraints.push((&left[&(i - 1, j)], 1));
            }
            if j < width {
                constraints.push((&top[&(i, j)], 1));
            }
            if j > 0 {
                constraints.push((&top[&(i, j - 1)], 1));
            }
            let zero = Bool::pb_eq(&ctx, &constraints, 0);
            let two = Bool::pb_eq(&ctx, &constraints, 2);
            solver.assert(&(zero | two));
            constraints.clear();
        }
    }
    let cell3 = *cells.iter().find(|(_, val)| **val == 3).unwrap().0;
    let (row, col) = (cell3 / width, cell3 % width);
    let mut dists = HashMap::new();
    for i in 0..=height {
        for j in 0..=width {
            dists.insert((i, j), BV::fresh_const(&ctx, "", 16));
        }
    }
    let zero = BV::from_u64(&ctx, 0, 16);
    let one = BV::from_u64(&ctx, 1, 16);
    for i in 0..=height {
        for j in 0..=width {
            let dist = dists.get(&(i, j)).unwrap();
            if i == row && j == col {
                solver.assert(&dist._eq(&zero));
                continue;
            }
            let mut constraints = Vec::with_capacity(5);
            let mut edges = Vec::with_capacity(4);
            if let Some(neighbor) = dists.get(&(i + 1, j)) {
                let edge = left.get(&(i, j)).unwrap();
                let cond = dist._eq(&(neighbor + &one));
                constraints.push(edge & &cond);
                edges.push(!edge);
            }
            if let Some(neighbor) = dists.get(&(i - 1, j)) {
                let edge = left.get(&(i - 1, j)).unwrap();
                let cond = dist._eq(&(neighbor + &one));
                constraints.push(edge & &cond);
                edges.push(!edge);
            }
            if let Some(neighbor) = dists.get(&(i, j + 1)) {
                let edge = top.get(&(i, j)).unwrap();
                let cond = dist._eq(&(neighbor + &one));
                constraints.push(edge & &cond);
                edges.push(!edge);
            }
            if let Some(neighbor) = dists.get(&(i, j - 1)) {
                let edge = top.get(&(i, j - 1)).unwrap();
                let cond = dist._eq(&(neighbor + &one));
                constraints.push(edge & &cond);
                edges.push(!edge);
            }
            let edges = edges.iter().collect::<Vec<_>>();
            constraints.push(Bool::and(&ctx, &edges));
            let constraints = constraints.iter().collect::<Vec<_>>();
            solver.assert(&Bool::or(&ctx, &constraints));
        }
    }

    assert_eq!(solver.check(), SatResult::Sat);
    let model = solver.get_model().unwrap();

    for i in 0..=height {
        for j in 0..width {
            let line = model.eval(&top[&(i, j)], false).unwrap().as_bool().unwrap();
            if line {
                print!("·───");
            } else {
                print!("·   ");
            }
        }
        println!("·  ");
        if i < height {
            for j in 0..=width {
                let cell = if j < width {
                    cells.get(&(width * i + j)).map(|c| (b'0' + c) as char).unwrap_or(' ')
                } else {
                    ' '
                };
                let line = model.eval(&left[&(i, j)], false).unwrap().as_bool().unwrap();
                if line {
                    print!("│ {} ", cell);
                } else {
                    print!("  {} ", cell);
                }
            }
        }
        println!();
    }
}
