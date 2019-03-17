use std::collections::{HashSet};

#[derive(Debug, Clone)]
struct Context(Vec<(Constructor, Vec<TermDescription>)>);


type MatchRule = Vec<(Pattern, i32)>;
type Rhs = i32;

/// Used to represent destructing of and object
#[derive(Debug, Clone)]
enum Access {
    /// The object
    Obj,
    /// A field of an object
    Sel(usize, Box<Access>),
}


#[derive(Debug, Clone)]
enum Decision {
    Failure,
    Success(Rhs),
    IfEq(Access, Constructor, Box<Decision>, Box<Decision>),
}

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
// True value
fn tt() -> Pattern {
    Pattern::Con(Constructor::new("true", 0, 2), vec![])
}

fn ff() -> Pattern {
    Pattern::Con(Constructor::new("false", 0, 2), vec![])
}

fn tup(args: Vec<Pattern>) -> Pattern {
    Pattern::Con(Constructor::new("tuple", args.len() as i32, 1), args)
}

fn nil() -> Pattern {
    Pattern::Con(Constructor::new("nil", 0, 2), vec![])
}

fn var(name: &str) -> Pattern {
    Pattern::Var(name.into())
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

    fn get_dargs(&mut self, i: usize) -> Vec<TermDescription> {
        match self {
            TermDescription::Neg(_) => (0..i)
                .map(|_| TermDescription::Neg(HashSet::new()))
                .collect(),
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
    work: &mut Vec<(Vec<Pattern>, Vec<Access>, Vec<TermDescription>)>,
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
fn fail(dsc: TermDescription, rules: &mut MatchRule) -> Decision {
    if rules.is_empty() {
        Decision::Failure
    } else {
        let (pat1, rhs1) = rules.remove(0);

        compile_match(
            pat1,
            Access::Obj,
            dsc,
            &mut Context::new(),
            &mut vec![],
            rhs1,
            rules,
        )
    }
}

fn succeed(
    ctx: &mut Context,
    work: &mut Vec<(Vec<Pattern>, Vec<Access>, Vec<TermDescription>)>,
    rhs: Rhs,
    rules: &mut MatchRule,
) -> Decision {
    if work.is_empty() {
        Decision::Success(rhs)
    } else {
        let mut work1 = work.remove(0);
        if work1.0.is_empty() && work1.1.is_empty() && work1.2.is_empty() {
            ctx.norm();
            succeed(ctx, work, rhs, rules)
        } else {
            let (pat1, obj1, desc1) = (work1.0.remove(0), work1.1.remove(0), work1.2.remove(0));
            work.insert(0, work1);
            compile_match(pat1, obj1, desc1, ctx, work, rhs, rules)
        }
    }
}


#[derive(Debug, Clone)]
enum MatchResult {
    Yes,
    No,
    Maybe,
}

fn static_match(pcon: &Constructor, dsc: &mut TermDescription) -> MatchResult {
    match dsc {
        TermDescription::Pos(ref con, _) => {
            if con == pcon {
                MatchResult::Yes
            } else {
                MatchResult::No
            }
        }

        TermDescription::Neg(ref mut cons) => {
            if cons.contains(pcon) {
                MatchResult::No
            } else if pcon.span as usize == (1 + cons.len()) {
                MatchResult::Yes
            } else {
                MatchResult::Maybe
            }
        }
    }
}

fn compile_match(
    pat1: Pattern,
    obj: Access,
    mut dsc: TermDescription,
    ctx: &mut Context,
    mut work: &mut Vec<(Vec<Pattern>, Vec<Access>, Vec<TermDescription>)>,
    rhs: Rhs,
    rules: &mut MatchRule,
) -> Decision {
    match pat1 {
        Pattern::Var(_) => {
            ctx.augment(dsc);
            succeed(ctx, work, rhs, rules)
        }
        Pattern::Con(ref pcon, ref pargs) => {
            match static_match(pcon, &mut dsc) {
                MatchResult::Yes => {
                    ctx.push((pcon.clone(), vec![]));
                    work.push((
                        pargs.clone(),
                        (0..pcon.arity)
                            .map(|i| Access::Sel((i + 1) as usize, Box::new(obj.clone())))
                            .collect(),
                        dsc.get_dargs(pcon.arity as usize),
                    ));
                    succeed(ctx, work, rhs, rules)
                }
                MatchResult::No => fail(build_dsc(ctx, dsc, &mut work), rules),
                MatchResult::Maybe => {
                    ctx.push((pcon.clone(), vec![]));

                    work.push((
                        pargs.clone(),
                        (0..pcon.arity)
                            .map(|i| Access::Sel((i + 1) as usize, Box::new(obj.clone())))
                            .collect(),
                        dsc.get_dargs(pcon.arity as usize),
                    ));

                    let lhs = Box::new(succeed(ctx, work, rhs, rules));

                    dsc.add_neg(pcon.clone());

                    Decision::IfEq(
                        obj,
                        pcon.clone(),
                        lhs,
                        Box::new(fail(build_dsc(ctx, dsc, &mut work), rules)),
                    )
                }
            }
        }
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

    let mut allmrules = vec![
        (
            tup(vec![
                tt(),
                Pattern::Con(Constructor::new("green", 0, 3), vec![]),
            ]),
            111,
        ),
        (
            tup(vec![
                ff(),
                Pattern::Con(Constructor::new("green", 0, 3), vec![]),
            ]),
            222,
        ),
    ];


    let mut allmrules = vec![
        (
            Pattern::Con(
                Constructor::new("Bob", 2, 3),
                vec![Pattern::Var("a".into()), Pattern::Var("b".into())],
            ),
            111,
        ),
        (
            Pattern::Con(
                Constructor::new("Busey", 1, 3),
                vec![Pattern::Con(
                    Constructor::new("Busey", 1, 3),
                    vec![Pattern::Var("z".into())],
                )],
            ),
            222,
        ),
        (
            Pattern::Con(
                Constructor::new("Busey", 1, 3),
                vec![Pattern::Con(
                    Constructor::new("Bob", 2, 3),
                    vec![Pattern::Var("x".into()), Pattern::Var("y".into())],
                )],
            ),
            333,
        ),
    ];

    //    let mut allmrules = vec![
    //        (
    //            tup(vec![var("x"),nil()]),
    //            111
    //        ),
    //        (
    //            tup(vec![nil(),var("x")]),
    //            222
    //        )
    //    ];

    println!(
        "{:#?}",
        fail(TermDescription::Neg(HashSet::new()), &mut allmrules)
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

        assert!(fail(TermDescription::Neg(HashSet::new()), &mut allmrules).is_some())
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
            fail(TermDescription::Neg(HashSet::new()), &mut allmrules),
            None
        )
    }
}
