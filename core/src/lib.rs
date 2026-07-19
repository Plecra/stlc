/// The interface of the Core language, defining the terms and types that the kernel checks

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    App(Box<Expr>, Box<Expr>),
    Abs(String, Box<Expr>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Base(String),
    Arrow(Box<Type>, Box<Type>),
}
