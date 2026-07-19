use ast::TypedEv;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    pub loc: usize,
    pub kind: ErrorKind,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    LambdaNameMissing,
    LambdaTypeColonMissing,
    UnclosedParen,
    BadType,
    BadExpr,
    LambdaDotMissing,
}
fn ws(src: &mut &[u8]) {
    while let [b' ' | b'\n', r @ ..] = *src {
        *src = r;
    }
}
fn ident(start: &[u8], src: &mut &[u8]) -> String {
    while let [b'a'..=b'z' | b'0'..=b'9' | b'_' | b'A'..=b'Z', r @ ..] = *src {
        *src = r;
    }
    String::from_utf8(start[..start.len() - src.len()].to_vec()).unwrap()
}
fn parse_ty_atom(src: &mut &[u8], errors: &mut Vec<Error>) -> core::Type {
    match *src {
        [b'a'..=b'z' | b'_' | b'A'..=b'Z', r @ ..] => {
            let n = *src;
            *src = r;
            let name = ident(n, src);
            ws(src);
            core::Type::Base(name)
        }
        [b'(', r @ ..] => {
            *src = r;
            let t1 = parse_ty(src, errors);
            if let [b')', r @ ..] = *src {
                *src = r;
                ws(src);
                t1
            } else {
                errors.push(Error {
                    loc: src.len(),
                    kind: ErrorKind::UnclosedParen,
                });
                t1
            }
        }
        _ => {
            errors.push(Error {
                loc: src.len(),
                kind: ErrorKind::BadType,
            });
            core::Type::Base("".to_string())
        }
    }
}
fn parse_ty(src: &mut &[u8], errors: &mut Vec<Error>) -> core::Type {
    let ty = parse_ty_atom(src, errors);
    match *src {
        [b'-', b'>', r @ ..] => {
            *src = r;
            ws(src);
            let t2 = parse_ty(src, errors);
            core::Type::Arrow(Box::new(ty), Box::new(t2))
        }
        _ => ty,
    }
}
fn parse_lam(src: &mut &[u8], errors: &mut Vec<Error>) -> TypedEv {
    let loc = src.len();
    let name = ident(src, src);
    if name.is_empty() {
        errors.push(Error {
            loc,
            kind: ErrorKind::LambdaNameMissing,
        });
    }
    ws(src);
    if let [b':', r @ ..] = *src {
        *src = r;
    } else {
        errors.push(Error {
            loc,
            kind: ErrorKind::LambdaTypeColonMissing,
        });
    };
    ws(src);
    let t = parse_ty(src, errors);
    if let [b'.', r @ ..] = *src {
        *src = r;
    } else {
        errors.push(Error {
            loc,
            kind: ErrorKind::LambdaDotMissing,
        });
    };
    ws(src);
    let body = parse_expr(src, errors);
    TypedEv::Abs(name, t, Box::new(body))
}
fn parse_expr_atom(src: &mut &[u8], errors: &mut Vec<Error>) -> TypedEv {
    match src {
        [b'a'..=b'z' | b'_' | b'A'..=b'Z', r @ ..] => {
            let n = *src;
            *src = r;
            let name = ident(n, src);
            ws(src);
            TypedEv::Var(name)
        }
        [b'(', r @ ..] => {
            *src = r;
            let ex = parse_expr(src, errors);
            if let [b')', r @ ..] = *src {
                *src = r;
                ws(src);
                ex
            } else {
                errors.push(Error {
                    loc: src.len(),
                    kind: ErrorKind::UnclosedParen,
                });
                ex
            }
        }
        _ => {
            errors.push(Error {
                loc: src.len(),
                kind: ErrorKind::BadExpr,
            });
            TypedEv::Var("".to_string())
        }
    }
}
fn parse_expr(src: &mut &[u8], errors: &mut Vec<Error>) -> TypedEv {
    let mut ex = match *src {
        [b'a'..=b'z' | b'_' | b'A'..=b'Z' | b'(', ..] => parse_expr_atom(src, errors),
        [b'\\', r @ ..] => {
            *src = r;
            return parse_lam(src, errors)
        },
        _ => todo!("{:?}", String::from_utf8_lossy(src)),
    };
    loop {
        match *src {
            [b'\\', r @ ..] => {
                *src = r;
                return TypedEv::App(Box::new(ex), Box::new(parse_lam(src, errors)));
            }
            [b'a'..=b'z' | b'_' | b'A'..=b'Z' | b'(', ..] => {
                let arg = parse_expr_atom(src, errors);
                ex = TypedEv::App(Box::new(ex), Box::new(arg));
            }
            _ => return ex,
        }
    }
}
pub fn parse(src: &mut &[u8]) -> (TypedEv, Vec<Error>) {
    let mut errors = Vec::new();
    ws(src);
    let ex = parse_expr(src, &mut errors);
    if !src.is_empty() {
        errors.push(Error {
            loc: src.len(),
            kind: ErrorKind::BadExpr,
        });
    }
    for e in &mut errors {
        e.loc = src.len() - e.loc;
    }
    (ex, errors)
}
