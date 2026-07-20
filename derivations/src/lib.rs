use ast::TypedEv;
use kernel::{Typed, Proof, Universe};

use std::collections::HashMap;
#[derive(Debug)]
pub struct ContextIndex(HashMap<String, Option<Proof<Universe>>>);

fn verify_universe(t: &core::Type) -> kernel::Proof<kernel::Universe> {
    match t {
        core::Type::Var(s) => kernel::Proof::type_var(s.clone()),
        core::Type::Arrow(a, b) => {
            kernel::Proof::arrow(verify_universe(a), verify_universe(b))
        },
        core::Type::Forall(param, body) => {
            forall(verify_universe(body), param.clone())
        }

    }
}
impl ContextIndex {
    fn consistent(&self, cx: &[String]) -> bool {
        cx.iter().all(|s| self.0.contains_key(s))
    }
    fn verify_ty(&self, ty: &core::Type) -> Result<Proof<Universe>, Error> {
        let univ = verify_universe(ty);
        if !self.consistent(&univ.get().context) {
            return Err(Error(()));
        }
        Ok(univ)
    }
    pub fn new(binds: impl Iterator<Item = (String, kernel::Bound)>) -> Result<Self, Error> {
        let mut this = ContextIndex(HashMap::new());
        for (s, b) in binds {
            this.0.insert(s, match b {
                kernel::Bound::TypeVar => None,
                kernel::Bound::Var(ty) => {
                    Some(this.verify_ty(&ty)?)
                },
            });
        }
        Ok(this)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(());
impl From<kernel::IncompatibleStep> for Error {
    fn from(_: kernel::IncompatibleStep) -> Self {
        Error(())
    }
}
/// [`kernel::Proof::app`] with automatic merging of the contexts of the function and argument.
pub fn app(f: Proof<Typed>, a: Proof<Typed>) -> Result<Proof<Typed>, Error> {
    let mut cx = vec![];
    let mut present = std::collections::HashSet::new();
    for (s, t) in f.get().context.iter().chain(&a.get().context) {
        if present.insert(s) {
            cx.push((s.clone(), t.clone()));
        }
    }
    Ok(f.structural(cx.clone())?.app(a.structural(cx)?)?)
}
/// [`kernel::Proof::poly_app`] with automatic merging of the contexts of the function and argument.
pub fn poly_app(f: Proof<Typed>, a: Proof<Universe>) -> Result<Proof<Typed>, Error> {
    let mut cx = vec![];
    let mut present = std::collections::HashSet::new();
    for (s, t) in f.get().context.iter().map(|(s, t)| (s, t)).chain(a.get().context.iter().map(|s| (s, &kernel::Bound::TypeVar))) {
        if present.insert(s) {
            cx.push((s.clone(), t.clone()));
        }
    }
    Ok(f.structural(cx.clone())?.poly_app(a)?)
}
/// [`kernel::Proof::abs`] with automatic exchange of the variable binding anywhere in the context.
pub fn abs(body: Proof<Typed>, param: String, ty: core::Type) -> Result<Proof<Typed>, Error> {
    let mut cx = body.get().context.clone();
    let n = cx.len() - 1;

    if let Some((i, (_, t))) = body
        .get()
        .context
        .iter()
        .enumerate()
        .find(|(_, (n, _))| n == &param)
    {
        if t != &kernel::Bound::Var(ty) {
            return Err(Error(()));
        }
        cx.swap(i, n);
    } else {
        cx.push((param, kernel::Bound::Var(ty)));
    }
    Ok(body.structural(cx)?.abs()?)
}
/// [`kernel::Proof::abs`] with automatic exchange of the variable binding anywhere in the context.
pub fn poly_abs(body: Proof<Typed>, param: String) -> Result<Proof<Typed>, Error> {
    let mut cx = body.get().context.clone();
    let n = cx.len() - 1;

    if let Some((i, (_, t))) = body
        .get()
        .context
        .iter()
        .enumerate()
        .find(|(_, (n, _))| n == &param)
    {
        if t != &kernel::Bound::TypeVar {
            return Err(Error(()));
        }
        cx.swap(i, n);
    } else {
        cx.push((param, kernel::Bound::TypeVar));
    }
    Ok(body.structural(cx)?.poly_abs()?)
}
/// [`kernel::Proof::forall`] with automatic exchange of the variable binding anywhere in the context.
pub fn forall(body: Proof<Universe>, param: String) -> Proof<Universe> {
    let mut cx = body.get().context.clone();
    let mut n = cx.len();

    for i in (0..cx.len()).rev() {
        if cx[i] == param {
            cx.swap(i, n - 1);
            n -= 1;
        }
    }
    if n == cx.len() {
        cx.push(param);
    } else {
        while n + 1 < cx.len() {
            cx.pop();
        }
    }
    body.structural_ty(cx).unwrap().forall().unwrap()
}
/// Verify a derivation against a context, producing a proof of its typing within
/// a subset of that context.
///
/// This function is logically pure: Any derivation that is well-typed will always
/// have the same typing in that context, and we can eg memoize `verify(cx, derivation)`
/// and store `HasType(derivation, ty)`.
///
/// The `cx` will be unchanged after this function returns.
pub fn verify(ev: &ast::TypedEv, cx: &mut ContextIndex) -> Result<Proof<Typed>, Error> {
    match ev {
        TypedEv::Var(n) => {
            cx.0.get(n)
                .and_then(|t| t.as_ref())
                .ok_or(Error(()))
                .and_then(|t| Ok(kernel::Proof::var(n.clone(), t.clone())?))
        }
        TypedEv::App(f, a) => {
            let ft = verify(f, cx)?;
            let at = verify(a, cx)?;
            app(ft, at)
        }
        TypedEv::PolyApp(f, ty) => {
            let ft = verify(f, cx)?;
            let substituted_ty = verify_universe(ty);
            poly_app(ft, substituted_ty)
        }
        TypedEv::PolyAbs(param, body) => {
            let old = cx.0.insert(param.clone(), None);
            let bt = verify(body, cx)?;
            if let Some(old) = old {
                cx.0.insert(param.clone(), old);
            } else {
                cx.0.remove(param);
            }
            poly_abs(bt, param.clone())
        }
        TypedEv::Abs(s, ty, b) => {
            let old = cx.0.insert(s.clone(), Some(cx.verify_ty(ty)?));
            let bt = verify(b, cx)?;
            if let Some(old) = old {
                cx.0.insert(s.clone(), old);
            } else {
                cx.0.remove(s);
            }
            abs(bt, s.clone(), ty.clone())
        }
    }
}
/// A convenient way to construct a derivation while verifying it.
pub struct RecordedProof(TypedEv, kernel::Proof<Typed>);
impl RecordedProof {
    pub fn evidence(&self) -> &TypedEv {
        &self.0
    }
    pub fn proof(&self) -> &kernel::Proof<Typed> {
        &self.1
    }
    pub fn into_inner(self) -> (TypedEv, kernel::Proof<Typed>) {
        (self.0, self.1)
    }
    pub fn show(ev: TypedEv, cx: &mut ContextIndex) -> Result<Self, Error> {
        let proof = verify(&ev, cx)?;
        Ok(RecordedProof(ev, proof))
    }
    pub fn var(name: String, ty: &core::Type) -> Result<Self, Error> {
        let ev = TypedEv::Var(name.clone());
        let proof = kernel::Proof::var(name, verify_universe(ty))?;
        Ok(RecordedProof(ev, proof))
    }
    pub fn app(self, arg: RecordedProof) -> Result<Self, Error> {
        let ev = TypedEv::App(Box::new(self.0), Box::new(arg.0));
        let proof = app(self.1, arg.1)?;
        Ok(RecordedProof(ev, proof))
    }
    pub fn abs(self, param: String, ty: core::Type) -> Result<Self, Error> {
        let ev = TypedEv::Abs(param.clone(), ty.clone(), Box::new(self.0));
        let proof = abs(self.1, param, ty)?;
        Ok(RecordedProof(ev, proof))
    }

    /// Check that the evidence verifies the proof.
    ///
    /// An error here indicates a bug in this module, and it can be used as a sanity
    /// check before serialization of the evidence.
    pub fn consistent(&self) -> Result<(), Error> {
        (verify(
            &self.0,
            &mut ContextIndex::new(self.1.get().context.iter().cloned())?,
        )?
        .get()
            == self.1.get())
        .then_some(())
        .ok_or(Error(()))
    }
}
