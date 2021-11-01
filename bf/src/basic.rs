use std::str::Chars;

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    MissingClose,
    ExtraClose,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AstOp {
    Incr,
    Decr,
    Left,
    Right,
    Loop(Vec<AstOp>),
    Read,
    Write,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Program(pub Vec<AstOp>);

pub fn parse(s: &str) -> Result<Program, ParseError> {
    fn parse_partial(mut iter: Chars, expect_close: bool) -> Result<(Program, Chars), ParseError> {
        let mut result = vec![];

        while let Some(c) = iter.next() {
            let op = match c {
                '+' => Some(AstOp::Incr),
                '-' => Some(AstOp::Decr),
                '>' => Some(AstOp::Right),
                '<' => Some(AstOp::Left),
                '.' => Some(AstOp::Write),
                ',' => Some(AstOp::Read),
                '[' => {
                    let (body, rest) = parse_partial(iter, true)?;
                    iter = rest;
                    Some(AstOp::Loop(body.0))
                }
                ']' => return Ok((Program(result), iter)),
                _ => None,
            };
            if let Some(op) = op {
                result.push(op)
            }
        }

        if expect_close {
            Err(ParseError::MissingClose)
        } else {
            Ok((Program(result), iter))
        }
    }

    let (result, mut iter) = parse_partial(s.chars(), false)?;
    if iter.any(|_| true) {
        Err(ParseError::ExtraClose)
    } else {
        Ok(result)
    }
}

pub fn basic_interpreter(prog: Program, stdin: impl Iterator<Item = u8>) -> Option<Vec<u8>> {
    let mut mem = vec![0u8];
    let mut stdout = Vec::new();
    let mut ptr = 0;

    fn run<I>(
        prog: &[AstOp],
        mut stdin: I,
        mem: &mut Vec<u8>,
        stdout: &mut Vec<u8>,
        ptr: &mut usize,
    ) -> Option<I>
    where
        I: Iterator<Item = u8>,
    {
        for op in prog {
            match op {
                AstOp::Decr => mem[*ptr] -= 1,
                AstOp::Incr => mem[*ptr] += 1,
                AstOp::Left => *ptr -= 1,
                AstOp::Right => {
                    *ptr += 1;
                    if *ptr >= mem.len() {
                        mem.push(0)
                    }
                }
                AstOp::Read => mem[*ptr] = stdin.next()?,
                AstOp::Write => stdout.push(mem[*ptr]),
                AstOp::Loop(body) => {
                    while mem[*ptr] != 0 {
                        stdin = run(body, stdin, mem, stdout, ptr)?
                    }
                }
            }
        }

        Some(stdin)
    }

    run(&prog.0, stdin, &mut mem, &mut stdout, &mut ptr)?;

    Some(stdout)
}

#[cfg(test)]
mod test {
    use super::{basic_interpreter, parse, AstOp::*, ParseError, Program};

    #[test]
    fn test_parse_basic() {
        assert_eq!(
            parse("+-hello world--,>><"),
            Ok(Program(vec![
                Incr, Decr, Decr, Decr, Read, Right, Right, Left
            ]))
        );
    }

    #[test]
    fn test_parse_loop_empty() {
        assert_eq!(parse("[]"), Ok(Program(vec![Loop(vec![])])));
    }
    #[test]
    fn test_parse_loop_basic() {
        assert_eq!(parse("[+]"), Ok(Program(vec![Loop(vec![Incr])])));
    }
    #[test]
    fn test_parse_loop_lead_trailed() {
        assert_eq!(
            parse("--[+-],"),
            Ok(Program(vec![Decr, Decr, Loop(vec![Incr, Decr]), Read]))
        );
    }
    #[test]
    fn test_parse_loop_nested() {
        assert_eq!(
            parse("--[+[-]],"),
            Ok(Program(vec![
                Decr,
                Decr,
                Loop(vec![Incr, Loop(vec![Decr])]),
                Read
            ]))
        );
    }
    #[test]
    fn test_parse_loop_missing_close() {
        assert_eq!(parse("--[+[-],"), Err(ParseError::MissingClose));
    }
    #[test]
    fn test_parse_loop_extra_close() {
        assert_eq!(parse("--+-],"), Err(ParseError::ExtraClose));
    }
    #[test]
    fn test_basic_interp() {
        assert_eq!(
            basic_interpreter(parse(",++-.>++.").unwrap(), vec![10].into_iter()).unwrap(),
            vec![11, 2]
        );
    }
    #[test]
    fn test_basic_interp_loop() {
        assert_eq!(
            basic_interpreter(parse("+++[-].").unwrap(), vec![10].into_iter()).unwrap(),
            vec![0]
        );
    }
}
