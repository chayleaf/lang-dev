/// A Lisp look-alike
use std::marker::PhantomData;

mod eval;
mod parse;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum LambdaArgs {
    Fix(Vec<String>),
    Var(String),
}

impl LambdaArgs {
    pub fn pprint(&self) -> String {
        match self {
            Self::Fix(args) => "(".to_owned() + &args.join(" ") + ")",
            Self::Var(args) => args.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Prim {
    Nil(PhantomData<bool>),
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),
    Cons(Box<Sexpr>, Box<Sexpr>),
    Lambda(LambdaArgs, Vec<Sexpr>),
    Macro(LambdaArgs, Vec<Sexpr>),
    Error(String),
}

impl Prim {
    pub fn pprint(&self, top_level: bool) -> String {
        match self {
            Self::Nil(_) => "nil".into(),
            Self::Bool(false) => "false".into(),
            Self::Bool(true) => "true".into(),
            Self::Int(x) => x.to_string(),
            Self::Float(x) => x.to_string(),
            Self::String(s) => {
                if !top_level {
                    "\"".to_owned() + &s.replace('"', "\\\"") + "\""
                } else {
                    s.clone()
                }
            }
            Self::Cons(a, b) => format!("(cons {} {})", a.pprint(false), b.pprint(false)),
            Self::Macro(args, code) => format!(
                "(macro {} {})",
                args.pprint(),
                code.iter()
                    .map(|x| x.pprint(false))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Self::Lambda(args, code) => format!(
                "(lambda {} {})",
                args.pprint(),
                code.iter()
                    .map(|x| x.pprint(false))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Self::Error(msg) => format!("(error \"{}\")", msg),
        }
    }
}

impl From<bool> for Prim {
    fn from(x: bool) -> Self {
        Self::Bool(x)
    }
}
impl From<i64> for Prim {
    fn from(x: i64) -> Self {
        Self::Int(x)
    }
}
impl From<f64> for Prim {
    fn from(x: f64) -> Self {
        Self::Float(x)
    }
}
impl From<String> for Prim {
    fn from(x: String) -> Self {
        Self::String(x)
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Sexpr {
    Builtin(String),
    List(Vec<Sexpr>),
    Prim(Prim),
    Var(String),
}

impl Sexpr {
    pub fn pprint(&self, top_level: bool) -> String {
        match self {
            Self::Builtin(s) => s.clone(),
            Self::Var(s) => s.clone(),
            Self::List(v) => {
                "(".to_owned()
                    + &v.iter()
                        .map(|x| x.pprint(false))
                        .collect::<Vec<_>>()
                        .join(" ")
                    + ")"
            }
            Self::Prim(prim) => prim.pprint(top_level),
        }
    }
}

fn main() {
    let code = std::env::args()
        .nth(1)
        .and_then(|x| std::fs::read_to_string(x).ok())
        .expect("Please provide a filename");
    println!(
        "Result: {:?}",
        eval::eval(
            &eval::global_ctx(),
            &parse::parse_sexpr(&format!(
                "(begin

{}

)",
                code
            ))
            .unwrap()
            .1
        )
        .unwrap_or_else(|err| err)
        .pprint(true)
    );
}
