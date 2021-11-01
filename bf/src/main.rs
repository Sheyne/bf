use egg::{Analysis, Applier, AstSize, EGraph, Extractor, Id, RecExpr, Rewrite, Runner, Var, define_language, rewrite as rw};

mod basic;

define_language! {
    enum MiddleBf {
        // (shift offset scoped then)
        "shift" = Shift([Id; 3]),
        // (offset-immediate offset amount then)
        "offset-immediate" = OffsetImmediate([Id; 3]),
        // (loop0 read-offset loop-body then)
        "loop0" = Loop0([Id; 3]),
        // (offset-n-times src-offset dest-offset amount then)
        "offset-n-times" = OffsetNTimes([Id; 4]),
        // (zero offset then)
        "zero" = Zero([Id; 2]),
        // (read offset then)
        "read" = Read([Id; 2]),
        // (write offset then)
        "write" = Write([Id; 2]),
        // nil
        "nil" = Nil,
        // num
        Num(i32),
        // bool
        Bool(bool),
    }
}

impl MiddleBf {
    fn num(&self) -> Option<i32> {
        match self {
            MiddleBf::Num(i) => Some(*i),
            _ => None,
        }
    }
    fn bool(&self) -> Option<bool> {
        match self {
            MiddleBf::Bool(i) => Some(*i),
            _ => None,
        }
    }
}

#[derive(Debug)]
struct MiddleInterpreter<'a> {
    memory: Vec<i32>,
    stdout: Vec<i32>,
    ptr: i32,
    prog: &'a RecExpr<MiddleBf>,
}

impl<'a> MiddleInterpreter<'a> {
    fn at_offset_mut(&mut self, offset: i32) -> &mut i32 {
        let idx = (self.ptr + offset) as usize;
        while idx >= self.memory.len() {
            self.memory.push(0);
        }
        &mut self.memory[idx]
    }

    fn from_id(&self, id: Id) -> &'a MiddleBf {
        &self.prog.as_ref()[Into::<usize>::into(id)]
    }

    fn run<I>(&mut self, mut expr: &'a MiddleBf, mut stdin: I) -> Option<I>
    where
        I: Iterator<Item = u8>,
    {
        let mut shift_back = 0;
        loop {
            expr = match expr {
                MiddleBf::Shift([offset, scoped, then]) => {
                    let offset = self.from_id(*offset).num()?;
                    let scoped = self.from_id(*scoped).bool()?;
                    let then = self.from_id(*then);
                    self.ptr += offset;
                    if scoped {
                        shift_back -= offset;
                    }
                    then
                }
                MiddleBf::OffsetImmediate([offset, amount, then]) => {
                    let offset = self.from_id(*offset).num()?;
                    let amount = self.from_id(*amount).num()?;
                    let then = self.from_id(*then);
                    *self.at_offset_mut(offset) += amount;
                    then
                }
                MiddleBf::Loop0([read_offset, loop_body, then]) => {
                    let read_offset = self.from_id(*read_offset).num()?;
                    let loop_body = self.from_id(*loop_body);
                    let then = self.from_id(*then);
                    while *self.at_offset_mut(read_offset) != 0 {
                        stdin = self.run(loop_body, stdin)?;
                    }
                    then
                }
                MiddleBf::OffsetNTimes([src_offset, dest_offset, amount, then]) => {
                    let src_offset = self.from_id(*src_offset).num()?;
                    let dest_offset = self.from_id(*dest_offset).num()?;
                    let amount = self.from_id(*amount).num()?;
                    let then = self.from_id(*then);
                    *self.at_offset_mut(dest_offset) += *self.at_offset_mut(src_offset) * amount;
                    then
                }
                MiddleBf::Read([offset, then]) => {
                    let offset = self.from_id(*offset).num()?;
                    let then = self.from_id(*then);
                    *self.at_offset_mut(offset) = stdin.next()? as i32;
                    then
                }
                MiddleBf::Write([offset, then]) => {
                    let offset = self.from_id(*offset).num()?;
                    let then = self.from_id(*then);
                    let value = *self.at_offset_mut(offset);
                    self.stdout.push(value);
                    then
                }
                MiddleBf::Nil => {
                    self.ptr += shift_back;
                    return Some(stdin);
                }
                MiddleBf::Num(_) => panic!("Evaluating a number"),
                MiddleBf::Bool(_) => panic!("Evaluating a bool"),
                MiddleBf::Zero([offset, then]) => {
                    let offset = self.from_id(*offset).num()?;
                    let then = self.from_id(*then);
                    *self.at_offset_mut(offset) = 0;
                    then
                }
            }
        }
    }
}

fn interpret_middle(prog: &RecExpr<MiddleBf>, stdin: impl Iterator<Item = u8>) -> Option<Vec<i32>> {
    let mut data = MiddleInterpreter {
        memory: Vec::new(),
        stdout: Vec::new(),
        ptr: 0,
        prog,
    };

    let y = prog.as_ref();
    data.run(&y[y.len() - 1], stdin)?;

    Some(data.stdout)
}

impl From<basic::Program> for RecExpr<MiddleBf> {
    fn from(program: basic::Program) -> Self {
        let mut result = RecExpr::default();
        let minus_1 = result.add(MiddleBf::Num(-1));
        let zero = result.add(MiddleBf::Num(0));
        let plus_1 = result.add(MiddleBf::Num(1));
        let false_n = result.add(MiddleBf::Bool(false));

        fn add_seq(
            result: &mut RecExpr<MiddleBf>,
            insts: impl DoubleEndedIterator<Item = basic::AstOp>,
            minus_1: Id,
            zero: Id,
            plus_1: Id,
            false_n: Id,
        ) -> Id {
            let mut prev = result.add(MiddleBf::Nil);
            for expr in insts.rev() {
                let e = match expr {
                    basic::AstOp::Incr => MiddleBf::OffsetImmediate([zero, plus_1, prev]),
                    basic::AstOp::Decr => MiddleBf::OffsetImmediate([zero, minus_1, prev]),
                    basic::AstOp::Left => MiddleBf::Shift([minus_1, false_n, prev]),
                    basic::AstOp::Right => MiddleBf::Shift([plus_1, false_n, prev]),
                    basic::AstOp::Loop(body) => MiddleBf::Loop0([
                        zero,
                        add_seq(result, body.into_iter(), minus_1, zero, plus_1, false_n),
                        prev,
                    ]),
                    basic::AstOp::Read => MiddleBf::Read([zero, prev]),
                    basic::AstOp::Write => MiddleBf::Write([zero, prev]),
                };
                prev = result.add(e);
            }

            prev
        }

        add_seq(
            &mut result,
            program.0.into_iter(),
            minus_1,
            zero,
            plus_1,
            false_n,
        );

        result
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct MergeOffsetImmediate {
    offset: Var,
    left: Var,
    right: Var,
    then: Var,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct MergeShift {
    left: Var,
    right: Var,
    then: Var,
    scoped: Var,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SwapShiftThenOffset {
    shift_o: Var,
    offset_o: Var,
    amount: Var,
    then: Var,
    scoped: Var,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ShiftAcrossLoop {
    offset: Var,
    loop_offset: Var,
    body: Var,
    then: Var,
    scoped: Var,
}

impl<T> Applier<MiddleBf, T> for MergeOffsetImmediate
where
    T: Analysis<MiddleBf>,
{
    fn apply_one(&self, egraph: &mut EGraph<MiddleBf, T>, _: Id, subst: &egg::Subst) -> Vec<Id> {
        let left = subst[self.left];
        let right = subst[self.right];

        let possible_lefts = egraph[left].iter().filter_map(|x| x.num());
        let possible_rights = egraph[right].iter().filter_map(|x| x.num());

        fn prove_one(mut x: impl Iterator<Item = i32>) -> Option<i32> {
            let z = x.next();
            let w = x.next();
            if w.is_none() {
                z
            } else {
                None
            }
        }

        let sum = match (prove_one(possible_lefts), prove_one(possible_rights)) {
            (Some(l), Some(r)) => Some(l + r),
            _ => None,
        };

        if let Some(sum) = sum {
            let offset = subst[self.offset];
            let then = subst[self.then];
            let sum = egraph.add(MiddleBf::Num(sum));
            vec![egraph.add(MiddleBf::OffsetImmediate([offset, sum, then]))]
        } else {
            vec![]
        }
    }
}

impl<T> Applier<MiddleBf, T> for MergeShift
where
    T: Analysis<MiddleBf>,
{
    fn apply_one(&self, egraph: &mut EGraph<MiddleBf, T>, _: Id, subst: &egg::Subst) -> Vec<Id> {
        let left = subst[self.left];
        let right = subst[self.right];

        let possible_lefts = egraph[left].iter().filter_map(|x| x.num());
        let possible_rights = egraph[right].iter().filter_map(|x| x.num());

        fn prove_one(mut x: impl Iterator<Item = i32>) -> Option<i32> {
            let z = x.next();
            let w = x.next();
            if w.is_none() {
                z
            } else {
                None
            }
        }

        let sum = match (prove_one(possible_lefts), prove_one(possible_rights)) {
            (Some(l), Some(r)) => Some(l + r),
            _ => None,
        };

        if let Some(sum) = sum {
            let then = subst[self.then];
            let scoped = subst[self.scoped];
            let sum = egraph.add(MiddleBf::Num(sum));
            vec![egraph.add(MiddleBf::Shift([sum, scoped, then]))]
        } else {
            vec![]
        }
    }
}

impl<T> Applier<MiddleBf, T> for SwapShiftThenOffset
where
    T: Analysis<MiddleBf>,
{
    fn apply_one(&self, egraph: &mut EGraph<MiddleBf, T>, _: Id, subst: &egg::Subst) -> Vec<Id> {
        let shift_o = subst[self.shift_o];
        let offset_o = subst[self.offset_o];

        let possible_lefts = egraph[shift_o].iter().filter_map(|x| x.num());
        let possible_rights = egraph[offset_o].iter().filter_map(|x| x.num());

        fn prove_one(mut x: impl Iterator<Item = i32>) -> Option<i32> {
            let z = x.next();
            let w = x.next();
            if w.is_none() {
                z
            } else {
                None
            }
        }

        let sum = match (prove_one(possible_lefts), prove_one(possible_rights)) {
            (Some(l), Some(r)) => Some(l + r),
            _ => None,
        };

        if let Some(sum) = sum {
            let then = subst[self.then];
            let scoped = subst[self.scoped];
            let amount = subst[self.amount];

            let sum = egraph.add(MiddleBf::Num(sum));
            let new_shift = egraph.add(MiddleBf::Shift([shift_o, scoped, then]));
            vec![egraph.add(MiddleBf::OffsetImmediate([sum, amount, new_shift]))]
        } else {
            vec![]
        }
    }
}

impl<T> Applier<MiddleBf, T> for ShiftAcrossLoop
where
    T: Analysis<MiddleBf>,
{
    fn apply_one(&self, egraph: &mut EGraph<MiddleBf, T>, _: Id, subst: &egg::Subst) -> Vec<Id> {
        let offset = subst[self.offset];
        let loop_offset = subst[self.loop_offset];

        let possible_lefts = egraph[offset].iter().filter_map(|x| x.num());
        let possible_rights = egraph[loop_offset].iter().filter_map(|x| x.num());

        fn prove_one(mut x: impl Iterator<Item = i32>) -> Option<i32> {
            let z = x.next();
            let w = x.next();
            if w.is_none() {
                z
            } else {
                None
            }
        }

        let sum = match (prove_one(possible_lefts), prove_one(possible_rights)) {
            (Some(l), Some(r)) => Some(l + r),
            _ => None,
        };

        if let Some(sum) = sum {
            let then = subst[self.then];
            let body = subst[self.body];
            let scoped = subst[self.scoped];

            let sum = egraph.add(MiddleBf::Num(sum));
            let tt = egraph.add(MiddleBf::Bool(true));

            let new_shift1 = egraph.add(MiddleBf::Shift([offset, tt, body]));
            let then = egraph.add(MiddleBf::Shift([offset, scoped, then]));
            vec![egraph.add(MiddleBf::Loop0([sum, new_shift1, then]))]
        } else {
            vec![]
        }
    }
}

fn main() {
    let puzzle = "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>>
    +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>+++++++>+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++>>>
    # the tape is now: {'y'|'e'|'s'|'\0'|'n'|'o'|'\0'|81|168|4|78|167|12|76|82|86|90|86|149|14|70|100|148|14|69|101|82|149|1|80|89|73|172|7|83|94|'\0'|'\0'|'\0'}
    
    >>>>>,<<<<<
    
    +
    
    >+++++++++++++++++++++++++++++{29}[-
        >[-]>[-]>[-]
        >[- <+> ]
    
        ,
    
        <<
    
        <<<<<
        <[[->+<]<]>>[>]<
        [- >>>>>+<<<<< ]
        >>>>>
    
        [- <->]
        >
        [- <<->> ]
        >
        >[-]<[- >+< <<<+>>> ]>[- <+> ]<
    
        <<<
    
        +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++{83}
    
        [[-]
            << [-] >>
        ]
    
        <
    ]
    
    <
    
    [
        <<<<
    ]
    <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
    
    [ .> ]";
    let hello_world = "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++.";
    let fib = ",>>+<<[>>[->+<]<[->+<]>>[-<+<+>>]<<<-]>.";
    let prog: RecExpr<MiddleBf> = basic::parse(fib).unwrap().into();

    let rules: &[Rewrite<MiddleBf, ()>] = &[
        rw!("re-order-offsets"; "(offset-immediate ?o1 ?a1 (offset-immediate ?o2 ?a2 ?then))" => "(offset-immediate ?o2 ?a2 (offset-immediate ?o1 ?a1 ?then))"),
        rw!("loop-transpose"; "(loop0 ?src (offset-immediate ?src -1 (offset-immediate ?dest ?amt nil)) ?then)" => "(offset-n-times ?src ?dest ?amt (zero ?src ?then))"),
        rw!("simplify-shifts"; "(shift ?o1 ?scoped (shift ?o2 ?scoped ?then))" => {MergeShift {
            left: "?o1".parse().unwrap(),
            right: "?o2".parse().unwrap(),
            then: "?then".parse().unwrap(),
            scoped: "?scoped".parse().unwrap(),
        }}),
        rw!("swap-shift-then-offset"; "(shift ?o ?scoped (offset-immediate ?oo ?a ?then))" => {SwapShiftThenOffset {
            shift_o: "?o".parse().unwrap(),
            offset_o: "?oo".parse().unwrap(),
            amount: "?a".parse().unwrap(),
            then: "?then".parse().unwrap(),
            scoped: "?scoped".parse().unwrap(),
        }}),
        rw!("sub-loop"; "(loop0 ?a (offset-immediate ?a -1 nil) ?then)" => "(zero ?a ?then)"),
        rw!("shift-across-loop"; "(shift ?scoped ?o (loop0 ?a ?body ?then))" => {ShiftAcrossLoop {
            offset: "?o".parse().unwrap(),
            loop_offset: "?a".parse().unwrap(),
            body: "?body".parse().unwrap(),
            then: "?then".parse().unwrap(),
            scoped: "?scoped".parse().unwrap(),
        }}),
        rw!("zero-shift"; "(shift 0 ?scoped ?then)" => "?then"),
        rw!("merge-offset-immediate"; "(offset-immediate ?x ?y (offset-immediate ?x ?z ?then))" => {MergeOffsetImmediate {
            offset: "?x".parse().unwrap(),
            left: "?y".parse().unwrap(),
            right: "?z".parse().unwrap(),
            then: "?then".parse().unwrap(),
        }}),
        rw!("offset-then-zero"; "(offset-immediate ?a ?g (zero ?a ?then))" => "(zero ?a ?then)"),
    ];

    let runner = Runner::default().with_expr(&prog).run(rules);

    let mut extractor = Extractor::new(&runner.egraph, AstSize);
    let (_, best_expr) = extractor.find_best(runner.roots[0]);

    println!("{}", best_expr.pretty(100));

    // for x in 0..20 {
    dbg!(interpret_middle(&best_expr, vec![5].into_iter()));
    // }
}
