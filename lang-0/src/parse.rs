use crate::{Prim, Sexpr};
use nom::{
    branch::alt,
    character::complete::{char, multispace0, none_of, one_of},
    combinator::{opt, recognize},
    error::ErrorKind,
    multi::{many0, many0_count, many1, many1_count},
    number::complete::double,
    sequence::{delimited, terminated, tuple},
    IResult,
};

#[derive(Debug, PartialEq)]
pub enum ParseError<I> {
    Int(I),
    Nom(I, ErrorKind),
}

impl<I> nom::error::ParseError<I> for ParseError<I> {
    fn from_error_kind(input: I, kind: ErrorKind) -> Self {
        ParseError::Nom(input, kind)
    }

    fn append(_: I, _: ErrorKind, other: Self) -> Self {
        other
    }
}

pub type Result<'a, T> = IResult<&'a str, T, ParseError<&'a str>>;

fn parse_list(input: &str) -> Result<Sexpr> {
    let (input, res) = delimited(
        terminated(char('('), multispace0),
        many0(terminated(parse_sexpr, multispace0)),
        terminated(char(')'), multispace0),
    )(input)?;
    Ok((input, Sexpr::List(res)))
}

fn parse_int(input: &str) -> Result<Prim> {
    let (input, res) = recognize(tuple((opt(char('-')), many1(one_of("0123456789")))))(input)?;
    let res = res
        .parse::<i64>()
        .map_err(|_| nom::Err::Error(ParseError::Int(input)))?;
    Ok((input, Prim::Int(res)))
}

fn parse_float(input: &str) -> Result<Prim> {
    let (input, res) = double(input)?;
    Ok((input, Prim::Float(res)))
}

fn parse_string(input: &str) -> Result<Prim> {
    let (input, res) =
        delimited(char('"'), recognize(many0_count(none_of("\""))), char('"'))(input)?;
    Ok((input, Prim::String(res.to_owned())))
}

fn parse_primitive(input: &str) -> Result<Sexpr> {
    let (input, res) = alt((parse_int, parse_float, parse_string))(input)?;
    Ok((input, Sexpr::Prim(res)))
}

fn parse_var(input: &str) -> Result<Sexpr> {
    let (input, res) = recognize(many1_count(none_of("\t \r\n()")))(input)?;
    Ok((input, Sexpr::Var(res.to_owned())))
}

pub fn parse_sexpr(input: &str) -> Result<Sexpr> {
    alt((parse_list, parse_primitive, parse_var))(input)
}
