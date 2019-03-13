use std::collections::{HashMap,HashSet};
use std::hash::Hash;

#[derive(Debug,Clone)]
struct Context(HashMap<Constructor,Vec<TermDescription>>);

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
    Pos(Constructor,Vec<TermDescription>),

    Neg(HashSet<Constructor>)
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
    pub fn add_neg(&mut self,con:Constructor) {
       match *self {
           TermDescription::Neg(ref mut nonset) => {
               if !nonset.contains(&con) && nonset.len()+1 < con.span as usize {
                    nonset.insert(con);
               }
           },
           _ => ()
       }
    }
}

impl Context {
    pub fn augment(&mut self,con:Constructor,desc:TermDescription) {

        match self.0.get_mut(&con) {
            Some(ref mut descs) => {
                descs.push(desc)
            },
            None => {
                self.0.insert(con,vec![]);
            }
        }
    }
}
/// Attempts to match the expression against each pattern from a rule in rules.
/// It succeeds with the rhs if the rule matches; it fails otherwise
fn fail(expr: Pattern, rules: &mut Vec<(Pattern, Pattern)>) -> Option<Pattern> {
    if rules.is_empty() {
        return None;
    } else {
        let (pat1, rhs1) = rules.remove(0);

        compile_match(pat1, expr, vec![], rhs1, rules)
    }
}

fn succeed(
    mut work: Vec<(Pattern, Pattern)>,
    rhs: Pattern,
    rules: &mut Vec<(Pattern, Pattern)>,
) -> Option<Pattern> {
    if work.is_empty() {
        Some(rhs)
    } else {
        let (pat1, obj1) = work.remove(0);

        compile_match(pat1, obj1, work, rhs, rules)
    }
}

enum MatchResult {
    Yes,
    No,
    Maybe
}

fn static_match(pcon:Constructor,dsc:TermDescription) -> MatchResult {
    match dsc {
        TermDescription::Pos(ref c,ref descs) => {
            if &pcon == c {
                MatchResult::Yes
            }else {
                MatchResult::No
            }
        },

        TermDescription::Neg(ref cons) => {
            if cons.contains(&pcon) {
                MatchResult::No
            }else if !cons.contains(&pcon) && pcon.span as usize == 1+cons.len() {
                MatchResult::Yes
            }else {
                MatchResult::Maybe
            }
        }
    }
}

fn compile_match(
    pat1: Pattern,
    obj1: Pattern,
    mut work: Vec<(Pattern, Pattern)>,
    rhs: Pattern,
    rules: &mut Vec<(Pattern, Pattern)>,
) -> Option<Pattern> {
    match pat1 {
        Pattern::Var(_) => succeed(work, rhs, rules),
        Pattern::Con(ref pcon, ref pargs) => match obj1 {
            Pattern::Con(ref ocon, ref oargs) => {
                if ocon == pcon {
                    let both = oargs
                        .clone()
                        .into_iter()
                        .zip(pargs.clone().into_iter())
                        .collect::<Vec<(Pattern, Pattern)>>();
                    work.extend(both);

                    succeed(work, rhs, rules)
                } else {
                    fail(obj1, rules)
                }
            }
            Pattern::Var(_) => succeed(work, rhs, rules),
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

    println!("{:#?}", fail(origobj, &mut allmrules))

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


        assert!(fail(origobj, &mut allmrules).is_some())
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


        assert_eq!(fail(origobj, &mut allmrules),None)
    }
}
