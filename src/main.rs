use std::collections::HashMap;
use z3::{Config, Context, SatResult, Solver};
use z3::ast::Bool;

enum Direction {
    Top,
    Right,
    Bottom,
    Left,
}

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
            idx += 1;
        } else {
            idx += 1 + (ch as usize) - ('a' as usize);
        }
    }

    let config = Config::new();
    let context = Context::new(&config);

    let mut top = HashMap::new();
    let mut left = HashMap::new();
    for i in 0..=height {
        for j in 0..=width {
            if i != height {
                left.insert((i, j), Bool::new_const(&context, format!("left_{}_{}", i, j)));
            }
            if j != width {
                top.insert((i, j), Bool::new_const(&context, format!("top_{}_{}", i, j)));
            }
        }
    }
    let solver = Solver::new(&context);
    for i in 0..height {
        for j in 0..width {
            if let Some(val) = cells.get(&(width * i + j)) {
                let constraint = Bool::pb_eq(&context, &[
                    (&top[&(i, j)], 1),
                    (&left[&(i, j)], 1),
                    (&top[&(i + 1, j)], 1),
                    (&left[&(i, j + 1)], 1),
                ], *val as i32);
                solver.assert(&constraint);
            }
        }
    }
    assert_eq!(solver.check(), SatResult::Sat);
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
            let zero = Bool::pb_eq(&context, &constraints, 0);
            let two = Bool::pb_eq(&context, &constraints, 2);
            solver.assert(&Bool::or(&context, &[&zero, &two]));
            constraints.clear();
        }
    }
    loop {
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

        let lines = top.values()
            .chain(left.values())
            .filter(|&bool| model.eval(bool, false).unwrap().as_bool().unwrap())
            .count();
        let mut min_chain = Vec::new();
        let mut min_chain_len = lines;
        for start in top.iter()
                .filter(|(_, bool)| model.eval(*bool, false).unwrap().as_bool().unwrap())
                .map(|(&coord, _)| coord) {
            let (mut i, mut j) = start;
            let mut chain = Vec::new();
            chain.push(&top[&(i, j)]);
            let mut dir = Direction::Top;
            while chain.len() <= 1 || chain.last() != chain.get(0) {
                match dir {
                    Direction::Top => {
                        if let Some(bool) = left.get(&(i-1, j+1)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                i -= 1;
                                j += 1;
                                dir = Direction::Left;
                                continue;
                            }
                        }
                        if let Some(bool) = top.get(&(i, j+1)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                j += 1;
                                dir = Direction::Top;
                                continue;
                            }
                        }
                        if let Some(bool) = left.get(&(i, j+1)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                dir = Direction::Right;
                                continue;
                            }
                        }
                    }
                    Direction::Right => {
                        if let Some(bool) = top.get(&(i+1, j+1)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                i += 1;
                                j += 1;
                                dir = Direction::Top;
                                continue;
                            }
                        }
                        if let Some(bool) = left.get(&(i+1, j+1)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                i += 1;
                                dir = Direction::Right;
                                continue;
                            }
                        }
                        if let Some(bool) = top.get(&(i+1, j)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                dir = Direction::Bottom;
                                continue;
                            }
                        }
                    }
                    Direction::Bottom => {
                        if let Some(bool) = left.get(&(i+1, j)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                i += 1;
                                j -= 1;
                                dir = Direction::Right;
                                continue;
                            }
                        }
                        if let Some(bool) = top.get(&(i+1, j-1)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                j -= 1;
                                dir = Direction::Bottom;
                                continue;
                            }
                        }
                        if let Some(bool) = left.get(&(i, j)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                dir = Direction::Left;
                                continue;
                            }
                        }
                    }
                    Direction::Left => {
                        if let Some(bool) = top.get(&(i, j-1)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                i -= 1;
                                j -= 1;
                                dir = Direction::Bottom;
                                continue;
                            }
                        }
                        if let Some(bool) = left.get(&(i-1, j)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                i -= 1;
                                dir = Direction::Left;
                                continue;
                            }
                        }
                        if let Some(bool) = top.get(&(i, j)) {
                            if model.eval(bool, false).unwrap().as_bool().unwrap() {
                                chain.push(bool);
                                dir = Direction::Top;
                                continue;
                            }
                        }
                    }
                }
            }
            chain.pop();
            if chain.len() < min_chain_len {
                min_chain = chain;
                min_chain_len = min_chain.len();
            }
        }

        println!("@@@@@@@@@@@@@@@@@@@@ min_chain.len() == {}, lines == {} @@@@@@@@@@@@@@@@@@@@", min_chain_len, lines);
        println!();
        if min_chain_len == lines {
            break;
        }
        solver.assert(&Bool::and(&context, &min_chain).not());
    }
}
