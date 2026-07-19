//! The interface of the Core language, defining the terms and types that the kernel checks

/// 
/// ## Literals
/// 
/// String and numerics literals are logically the same as extending the context with
/// families of variables typed with the literal's type.
/// `String : Type, "hello" : String |- "hello" : String`
/// `derivations::verify` can handle this by adding type expressions for String and Int
/// literals to the context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    App(Box<Expr>, Box<Expr>),
    Abs(String, Box<Expr>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(String),
    Arrow(Box<Type>, Box<Type>),
}
