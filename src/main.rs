#![feature(slice_patterns)]
use core::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, Clone)]
struct Context(Vec<(Constructor, Vec<TermDescription>)>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Value {
    True,
    False,
    String(String),
    Var(String),
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
struct TypeName(pub String);

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
struct Constructor {
    name: String,
    arity: i32,
    span: i32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TermDescription {
    Pos(Constructor, Vec<TermDescription>),

    Neg(HashSet<Constructor>),
}

fn tt() -> Pattern {
    Pattern::Con(Constructor::new("true", 0, 2), vec![])
}

fn ff() -> Pattern {
    Pattern::Con(Constructor::new("false", 0, 2), vec![])
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Pattern {
    Var(String),                    // e.g foo /vars
    Con(Constructor, Vec<Pattern>), //e.g. List(10,Nil)
}

impl Constructor {
    pub fn new(name: &str, arity: i32, span: i32) -> Self {
        Self {
            name: name.to_string(),
            arity,
            span,
        }
    }
}

impl TermDescription {
    pub fn add_neg(&mut self, con: Constructor) {
        match *self {
            TermDescription::Neg(ref mut nonset) => {
                if !nonset.contains(&con) && nonset.len() + 1 < con.span as usize {
                    nonset.insert(con);
                }
            }
            _ => (),
        }
    }

    fn get_dargs(&mut self) -> Vec<TermDescription> {
        match self {
            TermDescription::Neg(_) => vec![],
            TermDescription::Pos(_, dargs) => dargs.clone(),
        }
    }
}

impl Context {
    pub fn new() -> Self {
        Self(Vec::new())
    }
    pub fn augment(&mut self, desc: TermDescription) {
        if self.0.is_empty() {
            return;
        }

        let (con, mut args) = self.0.remove(0);

        args.push(desc);

        self.0.insert(0, (con, args));
    }

    pub fn norm(&mut self) {
        let (con, mut args) = self.0.remove(0);
        args.reverse();
        self.augment(TermDescription::Pos(con, args))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn push(&mut self, item: (Constructor, Vec<TermDescription>)) {
        self.0.push(item);
    }
}

fn build_dsc(
    ctx: &mut Context,
    dsc: TermDescription,
    work: &mut Vec<(Vec<Pattern>, Vec<Pattern>, Vec<TermDescription>)>,
) -> TermDescription {
    if ctx.is_empty() && work.is_empty() {
        dsc
    } else {
        let (con, mut args) = ctx.0.remove(0);
        let (_, _, mut dargs) = work.remove(0);

        dargs.insert(0, dsc);
        args.extend(dargs);
        args.reverse();

        build_dsc(ctx, TermDescription::Pos(con, args), work)
    }
}
/// Attempts to match the expression against each pattern from a rule in rules.
/// It succeeds with the rhs if the rule matches; it fails otherwise
fn fail(
    expr: Pattern,
    dsc: TermDescription,
    rules: &mut Vec<(Pattern, Pattern)>,
) -> Option<Pattern> {
    if rules.is_empty() {
        return None;
    } else {
        let (pat1, rhs1) = rules.remove(0);

        compile_match(pat1, expr, dsc, &mut Context::new(), vec![], rhs1, rules)
    }
}

fn succeed(
    ctx: &mut Context,
    mut work: Vec<(Vec<Pattern>, Vec<Pattern>, Vec<TermDescription>)>,
    rhs: Pattern,
    rules: &mut Vec<(Pattern, Pattern)>,
) -> Option<Pattern> {
    if work.is_empty() {
        Some(rhs)
    } else {
        let mut work1 = work.remove(0);

        if work1.0.is_empty() || work1.1.is_empty() || work1.2.is_empty() {
            ctx.norm();
            succeed(ctx, work, rhs, rules)
        } else {
            let (pat1, obj1, desc1) = (work1.0.remove(0), work1.1.remove(0), work1.2.remove(0));
            work.insert(0, work1);
            compile_match(pat1, obj1, desc1, ctx, work, rhs, rules)
        }
    }
}

enum MatchResult {
    Yes,
    No,
    Maybe,
}

fn static_match(pcon: &Constructor, dsc: &TermDescription) -> MatchResult {
    match dsc {
        TermDescription::Pos(ref c, ref descs) => {
            if pcon == c {
                MatchResult::Yes
            } else {
                MatchResult::No
            }
        }

        TermDescription::Neg(ref cons) => {
            if cons.contains(pcon) {
                MatchResult::No
            } else if !cons.contains(pcon) && pcon.span as usize == 1 + cons.len() {
                MatchResult::Yes
            } else {
                MatchResult::Maybe
            }
        }
    }
}

fn compile_match(
    pat1: Pattern,
    expr: Pattern,
    mut dsc: TermDescription,
    ctx: &mut Context,
    mut work: Vec<(Vec<Pattern>, Vec<Pattern>, Vec<TermDescription>)>,
    rhs: Pattern,
    rules: &mut Vec<(Pattern, Pattern)>,
) -> Option<Pattern> {
    match pat1 {
        Pattern::Var(_) => {
            ctx.augment(dsc);
            succeed(ctx, work, rhs, rules)
        }
        Pattern::Con(ref pcon, ref pargs) => match expr {
            Pattern::Con(ref ocon, ref oargs) => match static_match(pcon, &dsc) {
                MatchResult::Yes => {
                    ctx.push((pcon.clone(), vec![]));

                    work.push((pargs.clone(), oargs.clone(), dsc.get_dargs()));

                    succeed(ctx, work, rhs, rules)
                }
                MatchResult::No => fail(expr, build_dsc(ctx, dsc, &mut work), rules),
                MatchResult::Maybe => {
                    if ocon == pcon {
                        ctx.push((pcon.clone(), vec![]));

                        work.push((pargs.clone(), oargs.clone(), dsc.get_dargs()));

                        succeed(ctx, work, rhs, rules)
                    } else {
                        dsc.add_neg(pcon.clone());
                        fail(expr, dsc, rules)
                    }
                }
            },
            Pattern::Var(_) => {
                ctx.augment(dsc);
                succeed(ctx, work, rhs, rules)
            }
        },
    }
}

fn main() {
    //allmrules -refers to the decleration patterns
    //origobj refers to the match expression

    /*
    enum Billy {
            Bob(String,i32),
            Busey(Billy)
        }
    */

    let origobj = Pattern::Con(
        Constructor::new("Bob", 2, 3),
        vec![Pattern::Var("x".into()), Pattern::Var("y".into())],
    );

    let mut allmrules = vec![
        (
            Pattern::Con(
                Constructor::new("Bob", 2, 3),
                vec![Pattern::Var("a".into()), Pattern::Var("b".into())],
            ),
            tt(),
        ),
        (
            Pattern::Con(
                Constructor::new("Busey", 1, 3),
                vec![Pattern::Con(
                    Constructor::new("Busey", 1, 3),
                    vec![Pattern::Var("z".into())],
                )],
            ),
            ff(),
        ),
        (
            Pattern::Con(
                Constructor::new("Busey", 1, 3),
                vec![Pattern::Con(
                    Constructor::new("Bob", 2, 3),
                    vec![Pattern::Var("x".into()), Pattern::Var("y".into())],
                )],
            ),
            tt(),
        ),
    ];

    println!(
        "{:#?}",
        fail(
            origobj,
            TermDescription::Neg(HashSet::new()),
            &mut allmrules
        )
    )

    //example
    /*
        match billy {
            Bob(x,y) => {....},
            Busey(Busey (z)) => {....},
            Busey(Bob(x,y)) => {....},
        }
    */
}

#[cfg(test)]
mod test {
    use super::*;
    //    match billy {
    //        Bob(x,y) => {....},
    //        Busey(Busey (z)) => {....},
    //        Busey(Bob(x,y)) => {....},
    //    }
    #[test]
    fn it_works() {
        /*
        enum Billy {
                Bob(String,i32),
                Busey(Billy)
            }
        */

        let origobj = Pattern::Con(
            Constructor::new("Bob", 2, 3),
            vec![Pattern::Var("x".into()), Pattern::Var("y".into())],
        );

        let mut allmrules = vec![
            (
                Pattern::Con(
                    Constructor::new("Bob", 2, 3),
                    vec![Pattern::Var("a".into()), Pattern::Var("b".into())],
                ),
                tt(),
            ),
            (
                Pattern::Con(
                    Constructor::new("Busey", 1, 3),
                    vec![Pattern::Con(
                        Constructor::new("Busey", 1, 3),
                        vec![Pattern::Var("z".into())],
                    )],
                ),
                ff(),
            ),
            (
                Pattern::Con(
                    Constructor::new("Busey", 1, 3),
                    vec![Pattern::Con(
                        Constructor::new("Bob", 2, 3),
                        vec![Pattern::Var("x".into()), Pattern::Var("y".into())],
                    )],
                ),
                tt(),
            ),
        ];

        assert!(fail(
            origobj,
            TermDescription::Neg(HashSet::new()),
            &mut allmrules
        )
        .is_some())
    }

    /// Fails because of missing rule
    #[test]
    fn fails() {
        let origobj = Pattern::Con(
            Constructor::new("Bob", 2, 3),
            vec![Pattern::Var("x".into()), Pattern::Var("y".into())],
        );

        let mut allmrules = vec![
            (
                Pattern::Con(
                    Constructor::new("Busey", 1, 3),
                    vec![Pattern::Con(
                        Constructor::new("Busey", 1, 3),
                        vec![Pattern::Var("z".into())],
                    )],
                ),
                ff(),
            ),
            (
                Pattern::Con(
                    Constructor::new("Busey", 1, 3),
                    vec![Pattern::Con(
                        Constructor::new("Bob", 2, 3),
                        vec![Pattern::Var("x".into()), Pattern::Var("y".into())],
                    )],
                ),
                tt(),
            ),
        ];

        assert_eq!(
            fail(
                origobj,
                TermDescription::Neg(HashSet::new()),
                &mut allmrules
            ),
            None
        )
    }
}
