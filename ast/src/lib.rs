/// Evidence of a [`kernel::Typed`] judgement, intended to produce a [`kernel::Proof`].
/// These are capable of being serialized and later verified without trusting
/// the source of the evidence. TypedEv is defined to construct the contexts on demand,
/// to avoid needing verbose derivations that duplicate context entries at every step.
///
/// All proofs are constructed by the inference rules in the [`kernel`], so
/// the only consequence of a bug here or invalid evidence is that we'll reject
/// it when we verify it.
///
/// The particular structure of this evidence is flexible: We could easily
/// choose to have `App` nodes record the mapped context, or for `Var`s to use
/// a de Bruijn index instead of a name. DBIs are more efficient for the proof,
/// but force us to add a Weakening step that tracks the mapping of DBIs when we
/// want to reuse derivations in a larger context.
///
/// Another useful variant would capture structural alpha equivalence.
/// This version, however has an important property to demonstrate: It is the STLC.
///
/// When we ignore the `expr` part of the proven `Typed` judgements, we can see an
/// example of Curry-Howard.
/// We've got a system where programs *are* proofs of
/// `Entails(context, ty) := Typed(context, _, ty)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypedEv {
    Var(String),
    App(Box<TypedEv>, Box<TypedEv>),
    Abs(String, core::Type, Box<TypedEv>),
}
