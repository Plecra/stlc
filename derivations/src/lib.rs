use ast::TypedEv;

use std::collections::HashMap;
#[derive(Debug)]
pub struct ContextIndex(HashMap<String, core::Type>);
impl ContextIndex {
    pub fn new(binds: impl Iterator<Item = (String, core::Type)>) -> Self {
        ContextIndex(binds.collect())
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
pub fn app(f: kernel::Proof, a: kernel::Proof) -> Result<kernel::Proof, Error> {
    let mut cx = vec![];
    let mut present = std::collections::HashSet::new();
    for (s, t) in f.get().context.iter().chain(&a.get().context) {
        if present.insert(s) {
            cx.push((s.clone(), t.clone()));
        }
    }
    Ok(f.structural(cx.clone())?.app(a.structural(cx)?)?)
}
/// [`kernel::Proof::abs`] with automatic exchange of the variable binding anywhere in the context.
pub fn abs(body: kernel::Proof, param: String, ty: core::Type) -> Result<kernel::Proof, Error> {
    let mut cx = body.get().context.clone();
    let n = cx.len() - 1;

    if let Some((i, (_, t))) = body
        .get()
        .context
        .iter()
        .enumerate()
        .find(|(_, (n, _))| n == &param)
    {
        if t != &ty {
            return Err(Error(()));
        }
        cx.swap(i, n);
    } else {
        cx.push((param, ty));
    }
    Ok(body.structural(cx)?.abs()?)
}
/// Verify a derivation against a context, producing a proof of its typing within
/// a subset of that context.
///
/// This function is logically pure: Any derivation that is well-typed will always
/// have the same typing in that context, and we can eg memoize `verify(cx, derivation)`
/// and store `HasType(derivation, ty)`.
///
/// The `cx` will be unchanged after this function returns.
pub fn verify(ev: &ast::TypedEv, cx: &mut ContextIndex) -> Result<kernel::Proof, Error> {
    match ev {
        TypedEv::Var(n) => {
            cx.0.get(n)
                .map(|t| kernel::Proof::var(n.clone(), t.clone()))
                .ok_or(Error(()))
        }
        TypedEv::App(f, a) => {
            let ft = verify(f, cx)?;
            let at = verify(a, cx)?;
            app(ft, at)
        }
        TypedEv::Abs(s, ty, b) => {
            let old = cx.0.insert(s.clone(), ty.clone());
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
pub struct RecordedProof(TypedEv, kernel::Proof);
impl RecordedProof {
    pub fn evidence(&self) -> &TypedEv {
        &self.0
    }
    pub fn proof(&self) -> &kernel::Proof {
        &self.1
    }
    pub fn into_inner(self) -> (TypedEv, kernel::Proof) {
        (self.0, self.1)
    }
    pub fn show(ev: TypedEv, cx: &mut ContextIndex) -> Result<Self, Error> {
        let proof = verify(&ev, cx)?;
        Ok(RecordedProof(ev, proof))
    }
    pub fn var(name: String, ty: core::Type) -> Self {
        let ev = TypedEv::Var(name.clone());
        let proof = kernel::Proof::var(name, ty);
        RecordedProof(ev, proof)
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
            &mut ContextIndex::new(self.1.get().context.iter().cloned()),
        )?
        .get()
            == self.1.get())
        .then_some(())
        .ok_or(Error(()))
    }
}
