use std::{
    collections::HashMap,
    sync::{Arc, RwLock},
};

use crate::{LambdaArgs, Prim, Sexpr};

#[derive(Debug)]
pub struct Context {
    names: HashMap<String, Sexpr>,
    parent: Option<Ctx>,
    macro_context: bool,
}

impl Context {
    pub fn get(&self, name: &str) -> Option<Sexpr> {
        self.names.get(name).map(|x| (*x).clone()).or_else(|| {
            self.parent
                .as_ref()
                .and_then(|par| par.read().unwrap().get(name))
        })
    }
    pub fn set(&mut self, name: &str, val: Sexpr) {
        self.names.insert(name.to_owned(), val);
    }
    pub fn new_child(this: &Ctx) -> Ctx {
        RwLock::new(Context {
            parent: Some(this.clone()),
            names: HashMap::new(),
            macro_context: false,
        })
        .into()
    }
    pub fn new_macro_child(this: &Ctx) -> Ctx {
        RwLock::new(Context {
            parent: Some(this.clone()),
            names: HashMap::new(),
            macro_context: true,
        })
        .into()
    }
    pub fn unmacro(this: &Ctx) -> Ctx {
        if this.read().unwrap().macro_context {
            Context::unmacro(this.read().unwrap().parent.as_ref().unwrap())
        } else {
            this.clone()
        }
    }
}

pub type Ctx = Arc<RwLock<Context>>;

pub fn global_ctx() -> Ctx {
    RwLock::new(Context {
        parent: None,
        names: [
            ("#".into(), Sexpr::Builtin("comment".into())),
            ("+".into(), Sexpr::Builtin("+".into())),
            ("%".into(), Sexpr::Builtin("%".into())),
            ("-".into(), Sexpr::Builtin("-".into())),
            ("*".into(), Sexpr::Builtin("*".into())),
            ("/".into(), Sexpr::Builtin("/".into())),
            ("=".into(), Sexpr::Builtin("eq".into())),
            ("<".into(), Sexpr::Builtin("lt".into())),
            (">".into(), Sexpr::Builtin("gt".into())),
            (">=".into(), Sexpr::Builtin("ge".into())),
            ("=>".into(), Sexpr::Builtin("ge".into())),
            ("=<".into(), Sexpr::Builtin("le".into())),
            ("<=".into(), Sexpr::Builtin("le".into())),
            ("!=".into(), Sexpr::Builtin("ne".into())),
            ("~=".into(), Sexpr::Builtin("ne".into())),
            ("&".into(), Sexpr::Builtin("&".into())),
            ("|".into(), Sexpr::Builtin("|".into())),
            ("true".into(), Sexpr::Prim(Prim::Bool(true))),
            ("false".into(), Sexpr::Prim(Prim::Bool(false))),
            ("if".into(), Sexpr::Builtin("if".into())),
            ("apply".into(), Sexpr::Builtin("apply".into())),
            ("begin".into(), Sexpr::Builtin("begin".into())),
            ("do".into(), Sexpr::Builtin("begin_noscope".into())),
            ("define".into(), Sexpr::Builtin("define".into())),
            ("lambda".into(), Sexpr::Builtin("lambda".into())),
            ("macro".into(), Sexpr::Builtin("macro".into())),
            ("print".into(), Sexpr::Builtin("print".into())),
            ("println".into(), Sexpr::Builtin("println".into())),
            ("list".into(), Sexpr::Builtin("list".into())),
            ("eval".into(), Sexpr::Builtin("eval".into())),
            ("'".into(), Sexpr::Builtin("unquote".into())),
            ("exec".into(), Sexpr::Builtin("exec".into())),
            ("car".into(), Sexpr::Builtin("car".into())),
            ("cdr".into(), Sexpr::Builtin("cdr".into())),
            ("nil".into(), Sexpr::Prim(Prim::Nil(Default::default()))),
            ("cons".into(), Sexpr::Builtin("cons".into())),
        ]
        .into_iter()
        .collect(),
        macro_context: false,
    })
    .into()
}

enum Opt<T> {
    Some(T),
    Null,
    Undef,
}

impl<T> Opt<(bool, T)> {
    fn into_sexp(self) -> Opt<Sexpr> {
        match self {
            Opt::Some((a, _)) => Opt::Some(Sexpr::Prim(Prim::from(a))),
            Opt::Null => Opt::Null,
            Opt::Undef => Opt::Undef,
        }
    }
}

impl<T> Opt<T> {
    fn into_option(self) -> Option<T> {
        match self {
            Self::Some(a) => Some(a),
            _ => None,
        }
    }
}

macro_rules! compare_for_types {
    ($rest:expr, $op:expr, [$(($t1:ident, $t2:ident)),*]) => {
        $rest.iter().fold(Opt::Undef, |acc, x| {
            match (acc, x) {
                (Opt::Undef, x) => Opt::Some((true, x.clone())),
                (Opt::Some((false, x)), _) => Opt::Some((false, x)),
                $((Opt::Some((true, Sexpr::Prim(Prim::$t1(a)))), Sexpr::Prim(Prim::$t2(b))) => Opt::Some(($op(a, b), Sexpr::Prim(Prim::$t2(b.clone())))),)*
                _ => Opt::Null,
            }
        }).into_sexp().into_option().ok_or_else(|| Sexpr::Prim(Prim::Error("Invalid argument types".to_owned())))
    };
    ($rest:expr, [$(($t1:ident, $t2:ident, $op:expr)),*]) => {
        $rest.iter().fold(Opt::Undef, |acc, x| {
            match (acc, x) {
                (Opt::Undef, x) => Opt::Some((true, x.clone())),
                (Opt::Some((false, x)), _) => Opt::Some((false, x)),
                $((Opt::Some((true, Sexpr::Prim(Prim::$t1(a)))), Sexpr::Prim(Prim::$t2(b))) => Opt::Some(($op(a, b), Sexpr::Prim(Prim::$t2(b.clone())))),)*
                _ => Opt::Null,
            }
        }).into_sexp().into_option().ok_or_else(|| Sexpr::Prim(Prim::Error("Invalid argument types".to_owned())))
    };
}
macro_rules! fold_for_types {
    ($rest:expr, $op:expr, [$(($t1:ident, $t2:ident)),*]) => {
        $rest.iter().fold(Opt::Undef, |acc, x| {
            match (acc, x) {
                (Opt::Undef, x) => Opt::Some(x.clone()),
                $((Opt::Some(Sexpr::Prim(Prim::$t1(a))), Sexpr::Prim(Prim::$t2(b))) => Opt::Some(Sexpr::Prim($op(a, b))),)*
                _ => Opt::Null,
            }
        }).into_option().ok_or_else(|| Sexpr::Prim(Prim::Error("Invalid argument types".to_owned())))
    };
    ($rest:expr, [$(($t1:ident, $t2:ident, $op:expr)),*]) => {
        $rest.iter().fold(Opt::Undef, |acc, x| {
            match (acc, x) {
                (Opt::Undef, x) => Opt::Some(x.clone()),
                $((Opt::Some(Sexpr::Prim(Prim::$t1(a))), Sexpr::Prim(Prim::$t2(b))) => Opt::Some(Sexpr::Prim(Prim::from($op(a, b)))),)*
                _ => Opt::Null,
            }
        }).into_option().ok_or_else(|| Sexpr::Prim(Prim::Error("Invalid argument types".to_owned())))
    };
}

pub fn should_eval_args(fun: &Sexpr) -> bool {
    match fun {
        Sexpr::Builtin(s) => !matches!(
            s.as_str(),
            "define" | "macro" | "lambda" | "if" | "comment" | "begin" | "begin_noscope"
        ),
        Sexpr::Prim(Prim::Macro(..)) => false,
        _ => true,
    }
}

pub fn eval(ctx: &Ctx, exp: &Sexpr) -> Result<Sexpr, Sexpr> {
    let err = |s: &str| Sexpr::Prim(Prim::Error(s.to_owned()));
    match exp {
        Sexpr::Prim(_) | Sexpr::Builtin(_) => Ok(exp.clone()),
        Sexpr::Var(k) => ctx
            .read()
            .unwrap()
            .get(k)
            .ok_or_else(|| err(&format!("Name not in scope: {}", k))),
        Sexpr::List(x) => {
            let (first, rest) = x
                .split_first()
                .ok_or_else(|| err("Function name not provided"))?;
            let first = eval(ctx, first)?;
            let rest = if should_eval_args(&first) {
                rest.iter()
                    .map(|x| eval(ctx, x))
                    .collect::<Result<Vec<_>, _>>()?
            } else {
                rest.to_owned()
            };
            match first {
                Sexpr::Prim(Prim::Macro(LambdaArgs::Var(arg), code)) => {
                    let new_ctx = Context::new_macro_child(ctx);
                    {
                        let mut ctx = new_ctx.write().unwrap();
                        let mut args = Sexpr::Prim(Prim::Nil(Default::default()));
                        for arg in rest.iter().rev() {
                            args = Sexpr::Prim(Prim::Cons(Box::new(arg.clone()), Box::new(args)));
                        }
                        ctx.set(&arg, args);
                    }
                    let mut ret = None;
                    for x in code {
                        ret = Some(eval(&new_ctx, &x)?);
                    }
                    Ok(ret.unwrap())
                }
                Sexpr::Prim(Prim::Macro(LambdaArgs::Fix(args), code))
                    if args.len() == rest.len() =>
                {
                    let new_ctx = Context::new_macro_child(ctx);
                    {
                        let mut ctx = new_ctx.write().unwrap();
                        for (a, b) in args.iter().zip(rest.iter()) {
                            ctx.set(a, b.clone());
                        }
                    }
                    let mut ret = None;
                    for x in code {
                        ret = Some(eval(&new_ctx, &x)?);
                    }
                    Ok(ret.unwrap())
                }

                Sexpr::Prim(Prim::Lambda(LambdaArgs::Var(arg), code)) => {
                    let new_ctx = Context::new_child(ctx);
                    {
                        let mut ctx = new_ctx.write().unwrap();
                        let mut args = Sexpr::Prim(Prim::Nil(Default::default()));
                        for arg in rest.iter().rev() {
                            args = Sexpr::Prim(Prim::Cons(Box::new(arg.clone()), Box::new(args)));
                        }
                        ctx.set(&arg, args);
                    }
                    let mut ret = None;
                    for x in code {
                        ret = Some(eval(&new_ctx, &x)?);
                    }
                    Ok(ret.unwrap())
                }
                Sexpr::Prim(Prim::Lambda(LambdaArgs::Fix(args), code))
                    if args.len() == rest.len() =>
                {
                    let new_ctx = Context::new_child(ctx);
                    {
                        let mut ctx = new_ctx.write().unwrap();
                        for (a, b) in args.iter().zip(rest.iter()) {
                            ctx.set(a, b.clone());
                        }
                    }
                    let mut ret = None;
                    for x in code {
                        ret = Some(eval(&new_ctx, &x)?);
                    }
                    Ok(ret.unwrap())
                }
                Sexpr::Builtin(s) => {
                    match s.as_str() {
                        "car" => {
                            if let Some((arg, &[])) = rest.split_first() {
                                if let Sexpr::Prim(Prim::Cons(a, _)) = arg {
                                    Ok((**a).clone())
                                } else {
                                    Err(err("Argument type mismatch for car"))
                                }
                            } else {
                                Err(err("Argument count mismatch for car"))
                            }
                        }
                        "cdr" => {
                            if let Some((arg, &[])) = rest.split_first() {
                                if let Sexpr::Prim(Prim::Cons(_, b)) = arg {
                                    Ok((**b).clone())
                                } else {
                                    Err(err("Argument type mismatch for car"))
                                }
                            } else {
                                Err(err("Argument count mismatch for car"))
                            }
                        }
                        "cons" => {
                            let (a, rest) = rest
                                .split_first()
                                .ok_or_else(|| err("Argument count mismatch for cons"))?;
                            let b = if let Some((s, &[])) = rest.split_first() {
                                s
                            } else {
                                return Err(err("Argument count mismatch for cons"));
                            };
                            Ok(Sexpr::Prim(Prim::Cons(a.clone().into(), b.clone().into())))
                        }
                        "comment" => Ok(Sexpr::Prim(Prim::Nil(Default::default()))),
                        "apply" => {
                            let (fun, rest) = if let Some((s, rest)) = rest.split_first() {
                                (s, rest)
                            } else {
                                return Err(err("Argument count mismatch for apply"));
                            };
                            if let Some((arg, &[])) = rest.split_first() {
                                let mut arg = arg;
                                let mut args = vec![fun.clone()];
                                loop {
                                    match arg {
                                        Sexpr::Prim(Prim::Nil(_)) => break,
                                        Sexpr::Prim(Prim::Cons(a, b)) => {
                                            args.push((**a).clone());
                                            arg = &*b;
                                        }
                                        _ => return Err(err("Argument type mismatch for apply")),
                                    }
                                }
                                eval(ctx, &Sexpr::List(args))
                            } else {
                                Err(err("Invalid arguments provided to apply"))
                            }
                        }
                        "print" => {
                            print!(
                                "{}",
                                rest.iter()
                                    .map(|x| x.pprint(true))
                                    .collect::<Vec<_>>()
                                    .join("")
                            );
                            Ok(Sexpr::Prim(Prim::Nil(Default::default())))
                        }
                        "println" => {
                            println!(
                                "{}",
                                rest.iter()
                                    .map(|x| x.pprint(true))
                                    .collect::<Vec<_>>()
                                    .join(" ")
                            );
                            Ok(Sexpr::Prim(Prim::Nil(Default::default())))
                        }
                        "define" => {
                            let (name, rest) =
                                if let Some((Sexpr::Var(s), rest)) = rest.split_first() {
                                    (s, rest)
                                } else {
                                    return Err(err("Invalid name for define"));
                                };
                            let other = if let Some((s, &[])) = rest.split_first() {
                                eval(ctx, s)?
                            } else {
                                return Err(err(&format!("Definition not provided for {}", name)));
                            };
                            ctx.write().unwrap().set(name, other);
                            Ok(Sexpr::Prim(Prim::Nil(Default::default())))
                        }
                        "exec" => {
                            if let Some((Sexpr::Prim(Prim::String(s)), &[])) = rest.split_first() {
                                eval(
                                    ctx,
                                    &crate::parse::parse_sexpr(&format!("(do {})", s))
                                        .map_err(|e| err(&format!("Parse error: {:?}", e)))?
                                        .1,
                                )
                            } else {
                                Err(err("Invalid arguments for eval"))
                            }
                        }
                        "eval" => {
                            if let Some((Sexpr::Prim(Prim::String(s)), &[])) = rest.split_first() {
                                eval(
                                    &Context::new_child(ctx),
                                    &crate::parse::parse_sexpr(s)
                                        .map_err(|e| err(&format!("Parse error: {:?}", e)))?
                                        .1,
                                )
                            } else {
                                Err(err("Invalid arguments for eval"))
                            }
                        }
                        "unquote" => {
                            if let Some((s, &[])) = rest.split_first() {
                                eval(&Context::unmacro(ctx), s)
                            } else {
                                Err(err("Invalid arguments for eval"))
                            }
                        }
                        "begin" => {
                            let ctx = Context::new_child(ctx);
                            let res = rest
                                .iter()
                                .map(|x| eval(&ctx, x))
                                .collect::<Result<Vec<_>, _>>()?;
                            Ok(res
                                .iter()
                                .next_back()
                                .cloned()
                                .unwrap_or_else(|| Sexpr::Prim(Prim::Nil(Default::default()))))
                        }
                        "begin_noscope" => {
                            let res = rest
                                .iter()
                                .map(|x| eval(ctx, x))
                                .collect::<Result<Vec<_>, _>>()?;
                            Ok(res
                                .iter()
                                .next_back()
                                .cloned()
                                .unwrap_or_else(|| Sexpr::Prim(Prim::Nil(Default::default()))))
                        }
                        "if" => {
                            let (cond, rest) = if let Some((cond, rest)) = rest.split_first() {
                                (eval(ctx, cond)?, rest)
                            } else {
                                return Err(err("Condition not provided for if"));
                            };
                            if !matches!(rest.len(), 0..=2) {
                                return Err(err("Invalid branch count for if"));
                            }
                            let cond = if let Sexpr::Prim(Prim::Bool(x)) = cond {
                                x
                            } else {
                                return Err(err("Invalid condition type for if"));
                            };
                            if cond {
                                eval(ctx, &rest[0])
                            } else {
                                rest.get(1).map(|x| eval(ctx, x)).unwrap_or_else(|| {
                                    Ok(Sexpr::Prim(Prim::Nil(Default::default())))
                                })
                            }
                        }
                        "lambda" => {
                            let (names, rest) = match rest.split_first() {
                                Some((Sexpr::List(s), rest)) => (
                                    LambdaArgs::Fix(
                                        s.iter()
                                            .map(|x| {
                                                if let Sexpr::Var(v) = x {
                                                    Some(v.clone())
                                                } else {
                                                    None
                                                }
                                            })
                                            .collect::<Option<Vec<_>>>()
                                            .ok_or_else(|| {
                                                err("Invalid lambda argument declaration")
                                            })?,
                                    ),
                                    rest,
                                ),
                                Some((Sexpr::Var(s), rest)) => (LambdaArgs::Var(s.clone()), rest),
                                _ => return Err(err("Invalid lambda argument declaration")),
                            };
                            let rest = rest.to_vec();
                            Ok(Sexpr::Prim(Prim::Lambda(names, rest)))
                        }
                        "macro" => {
                            let (names, rest) = match rest.split_first() {
                                Some((Sexpr::List(s), rest)) => (
                                    LambdaArgs::Fix(
                                        s.iter()
                                            .map(|x| {
                                                if let Sexpr::Var(v) = x {
                                                    Some(v.clone())
                                                } else {
                                                    None
                                                }
                                            })
                                            .collect::<Option<Vec<_>>>()
                                            .ok_or_else(|| {
                                                err("Invalid macro argument declaration")
                                            })?,
                                    ),
                                    rest,
                                ),
                                Some((Sexpr::Var(s), rest)) => (LambdaArgs::Var(s.clone()), rest),
                                _ => return Err(err("Invalid macro argument declaration")),
                            };
                            let rest = rest.to_vec();
                            Ok(Sexpr::Prim(Prim::Macro(names, rest)))
                        }
                        "+" => fold_for_types!(
                            rest,
                            [
                                (String, String, |a, b| a + b),
                                (Int, Int, |a, b| a + b),
                                (Float, Float, |a, b| a + b),
                                (Int, Float, |a, b| a as f64 + b),
                                (Float, Int, |a, b: &i64| a + *b as f64)
                            ]
                        ),
                        "-" => fold_for_types!(
                            rest,
                            [
                                (Int, Int, |a, b| a - b),
                                (Float, Float, |a, b| a - b),
                                (Float, Int, |a, b: &i64| a - *b as f64),
                                (Int, Float, |a, b| a as f64 - b)
                            ]
                        ),
                        "*" => fold_for_types!(
                            rest,
                            [
                                (Int, Int, |a, b| a * b),
                                (Float, Float, |a, b| a * b),
                                (Float, Int, |a, b: &i64| a * *b as f64),
                                (Int, Float, |a, b| a as f64 * b)
                            ]
                        ),
                        "/" => fold_for_types!(
                            rest,
                            [
                                (Int, Int, |a, b| a / b),
                                (Float, Float, |a, b| a / b),
                                (Float, Int, |a, b: &i64| a / *b as f64),
                                (Int, Float, |a, b| a as f64 / b)
                            ]
                        ),
                        "eq" => Ok(Sexpr::Prim(Prim::Bool(
                            rest.windows(2).all(|x| x[0].eq(&x[1])),
                        ))),
                        "ne" => Ok(Sexpr::Prim(Prim::Bool(
                            rest.windows(2).all(|x| x[0].ne(&x[1])),
                        ))),
                        "lt" => {
                            compare_for_types!(
                                rest,
                                [
                                    (String, String, |a, b| &a < b),
                                    (Int, Int, |a, b| &a < b),
                                    (Float, Float, |a, b| &a < b),
                                    (Int, Float, |a, b| &(a as f64) < b),
                                    (Float, Int, |a, b: &i64| a < *b as f64)
                                ]
                            )
                        }
                        // TODO: other comparison ops
                        _ => Err(err("Unimplemented")),
                    }
                }
                // Non-function
                _ => Err(err(&format!("Unable to evaluate {:?}", first))),
            }
        }
    }
}
