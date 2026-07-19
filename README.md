# Type checking

A simple demonstration of structuring a type checker around a kernel: This project typechecks lambda calculus terms with simple types, using STLC terms as derivations that can be verified.

The `kernel` module defines the typing judgement very similarly to the LCF style of proof kernel.

### Project layout

- `core` defines the core language's terms and types. It's a simple AST definition
- `kernel` defines a typing judgment on core. It only exposes a sound interface, so that all typing judgements must be proven using the kernel's inference rules.
- `ast` defines the syntax of our proof derivations, which we can use to construct proofs in the `kernel`. This allows these derivations to be serialized and transferred without being trusted like the kernel proofs.
- `derivations` uses a derivation to prove a typing judgement, adding automatic inference for the structural rules.
- `parser` provides a parser to translate STLC terms into our derivations
- `demo` has a few runnable examples for proving typing judgements

In particular, this isolates the inference algorithm from the type checker itself. An alternative parser could parse a different syntax with inferred lambda types and reuse the kernel and derivation type.