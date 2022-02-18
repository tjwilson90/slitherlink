use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use quick_xml::events::Event;
use quick_xml::events::attributes::Attributes;
use quick_xml::Reader;
use z3::{Config, Context, SatResult, Solver};
use z3::ast::Bool;

enum Direction {
    Top,
    Right,
    Bottom,
    Left,
}

fn is_cell(attrs: Attributes) -> Result<bool, Box<dyn Error>> {
    for attr in attrs {
        let attr = attr?;
        if attr.key == b"class" && attr.value.as_ref().starts_with(b"loop-task-cell") {
            return Ok(true)
        }
    }
    Ok(false)
}

fn style(attrs: Attributes) -> Result<Cow<'_, [u8]>, Box<dyn Error>> {
    for attr in attrs {
        let attr = attr?;
        if attr.key == b"style" {
            return Ok(attr.value)
        }
    }
    panic!("no style")
}

fn parse(bytes: &[u8]) -> u8 {
    let mut val = 0;
    for b in bytes {
        val = 10 * val + (*b - b'0');
    }
    val
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut reader = Reader::from_file("/Users/twilson/code/slitherlink/slither.html")?;
    reader.trim_text(true);
    let mut buf = Vec::new();
    let config = Config::new();
    let context = Context::new(&config);
    let mut cells = HashMap::new();
    let mut width = HashSet::new();
    let mut height = HashSet::new();
    let mut i = 0;
    loop {
        match reader.read_event(&mut buf)? {
            Event::Start(e) | Event::Empty(e) => {
                if is_cell(e.attributes())? {
                    i += 1;
                    let style = style(e.attributes())?;
                    let style = style.as_ref();
                    for style in style.split(|&b| b == b';') {
                        if style.starts_with(b" top:") {
                            height.insert(String::from_utf8_lossy(style).into_owned());
                        } else if style.starts_with(b" left:") {
                            width.insert(String::from_utf8_lossy(style).into_owned());
                        }
                    }
                }
            }
            Event::Text(e) => {
                cells.insert(i - 1, parse(&e));
            }
            Event::End(_) | Event::CData(_) | Event::Comment(_) => {} | Event::Decl(_) | Event::PI(_) | Event::DocType(_) => continue,
            Event::Eof => break,
        }
        buf.clear();
    }
    let width = width.len();
    let height = height.len();
    println!("width={}, height={}", width, height);

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
                        cells.get(&(width * i + j)).map(|c| (b'0' + *c) as char).unwrap_or(' ')
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
    Ok(())
}
