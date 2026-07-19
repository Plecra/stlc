use core::{Expr, Type};
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bound {
    Var(Type),
    TypeVar,
}
pub type Context = Vec<(String, Bound)>;
pub type TypeContext = Vec<String>;
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Typed {
    pub context: Context,
    pub expr: Expr,
    pub ty: Type,
}
#[allow(non_snake_case)]
fn Typed(context: Context, expr: Expr, ty: Type) -> Typed {
    Typed { context, expr, ty }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Universe {
    pub context: TypeContext,
    pub ty: Type,
}
/// A proof of a [`Typed`] judgement, built from the inference rules defined
/// on this type.
///
/// This is the ground truth of the type checker: An expression 'truly' has a type
/// if and only if there exists a `Proof` of the judgement that the expression has that type.
///
/// # Meaning
///
/// A slightly more direct interpretation of inference rules is as parameterized rules:
///
/// ```ignore
/// fn app(context: Vec<(String, Type)>, f: Expr, a: Expr, at: Type, ret: Type) -> Rule {
///     Rule(
///         Typed(context.clone(), Expr::App(Box::new(f.clone()), Box::new(a.clone())), ret.clone()),
///         vec![
///             Typed(context.clone(), f, Type::Arrow(Box::new(at.clone()), Box::new(ret))),
///             Typed(context, a, at),
///         ],
///     )
/// }
/// ```
///
/// This is to say that if we have the typing for f and a at the appropriate types, we can
/// type their application. We can then eliminate the premises by providing a `Proof(t)` equal
/// to the required premise. [`Proof::app`] does this in a single step to at least avoid *this* much
/// inefficiency: It instead directly takes the proofs of the premises, checking them computationally
/// without ever materializing a copy of the `Typed` judgements. The premises also fix some of the
/// rule's parameters so we avoid redundantly passing them as well. (For these STLC rules, app and abs'
/// premises both entirely fix their parameters)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof<T>(T);

impl<T> Proof<T> {
    pub fn get(&self) -> &T {
        &self.0
    }
    pub fn into_inner(self) -> T {
        self.0
    }
}

#[derive(Debug)]
pub struct IncompatibleStep(());
impl Proof<Typed> {
    /// ```ignore
    /// x : A |- x : A
    /// ```
    pub fn var(name: String, ty: Proof<Universe>) -> Result<Self, IncompatibleStep> {
        let mut context = ty.0.context.into_iter().map(|s| (s, Bound::TypeVar)).collect::<Vec<_>>();
        if context.iter().any(|(tyname, _)| tyname == &name) {
            return Err(IncompatibleStep(()));
        }
        context.push((name.clone(), Bound::Var(ty.0.ty.clone())));
        Ok(Proof(Typed(context, Expr::Var(name), ty.0.ty)))
    }
    /// ```ignore
    /// cx |- f : A -> B
    /// cx |- e : A
    /// ---
    /// cx |- f e : B
    /// ```
    pub fn app(self, arg: Proof<Typed>) -> Result<Self, IncompatibleStep> {
        let (context, b_ty, f, e) = match self.0.ty {
            Type::Arrow(argt, rett) if (&arg.0.context, &arg.0.ty) == (&self.0.context, &*argt) => {
                (arg.0.context, *rett, self.0.expr, arg.0.expr)
            }
            _ => return Err(IncompatibleStep(())),
        };
        Ok(Proof(Typed(
            context,
            Expr::App(Box::new(f), Box::new(e)),
            b_ty,
        )))
    }
    /// ```ignore
    /// cx, x: A |- e : B
    /// ---
    /// cx |- (\x. e) : A -> B
    /// ```
    pub fn abs(mut self) -> Result<Self, IncompatibleStep> {
        let (param, t) = self.0.context.pop().ok_or(IncompatibleStep(()))?;
        Ok(Proof(Typed(
            self.0.context,
            Expr::Abs(param, Box::new(self.0.expr)),
            Type::Arrow(Box::new(match t {
                Bound::Var(ty) => ty,
                _ => return Err(IncompatibleStep(())),
            }), Box::new(self.0.ty)),
        )))
    }
    /// We capture the weakening and contraction rules in a single verification step:
    /// performing simultaneous exchange of the context while introducing new bindings
    ///
    /// ```ignore
    /// cx |- e : A
    /// |- cx, cx2
    /// ---
    /// cx, cx2 |- e : A
    /// ```
    ///
    /// ```ignore
    /// cx, x : T, y : U, cx2 |- e : A
    /// ---
    /// cx, y : U, x : T, cx2 |- e : A
    /// ```
    pub fn structural(self, context: Vec<(String, Bound)>) -> Result<Self, IncompatibleStep> {
        use std::collections::HashMap;
        // note: this same logic can be implemented 'syntactically' by
        //     forall i in context, forall j, i < j ==> context[i].name != context[j].name
        //     forall (s, t) in old_context, forall (s2, t2) in context, s == s2 ==> t == t2
        // The hashmap is used here as a sensible optimization.
        let index = context
            .iter()
            .map(|(s, t)| (&**s, t))
            .collect::<HashMap<_, _>>();

        // Check that the context is well formed. That just means that the names are unique here.
        if index.len() != context.len()
        // And require that all the bindings in the proof's context are identically mapped.
        || !self.get().context.iter().all(|(s, b)| index.get(&**s) == Some(&b))
        {
            return Err(IncompatibleStep(()));
        }
        Ok(Proof(Typed(context, self.0.expr, self.0.ty)))
    }
}

/// In this basic form, this is a little silly: *all* types are in the universe and we're just
/// collecting the free variables.
impl Proof<Universe> {
    pub fn type_var(name: String) -> Self {
        Proof(Universe {
            context: vec![name.clone()],
            ty: Type::Var(name),
        })
    }
    pub fn arrow(self, arg: Self) -> Self {
        let mut context = self.0.context;
        context.extend(arg.0.context);
        Proof(Universe {
            context,
            ty: Type::Arrow(Box::new(self.0.ty), Box::new(arg.0.ty)),
        })
    }
}