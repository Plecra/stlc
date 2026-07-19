# Type checking

A simple demonstration of structuring a type checker around a kernel: This project typechecks lambda calculus terms with simple types, using STLC terms as derivations that can be verified.

The `kernel` module defines the typing judgement very similarly to the LCF style of proof kernel.

Oh and - dont let the 6 modules scare you off. The actual implementation here is tiny, but this is written
as a skeleton for writing larger languages in, where the distinction between these components is more useful,
and we want to be able to depend on the individual components more easily.

### Project layout

- `core` defines the core language's terms and types. It's a simple AST definition
- `kernel` defines a typing judgment on core. It only exposes a sound interface, so that all typing judgements must be proven using the kernel's inference rules.
- `ast` defines the syntax of our proof derivations, which we can use to construct proofs in the `kernel`. This allows these derivations to be serialized and transferred without being trusted like the kernel proofs.
- `derivations` uses a derivation to prove a typing judgement, adding automatic inference for the structural rules.
- `parser` provides a parser to translate STLC terms into our derivations
- `demo` has a few runnable examples for proving typing judgements

In particular, this isolates the inference algorithm from the type checker itself. An alternative parser could parse a different syntax with inferred lambda types and reuse the kernel and derivation type.

## Why?

For more complex type system features, the inference rules can sometimes be a bit tricky to protect as the implementation of the type checker grows, so using proof kernels can be pretty appealing. All typing judgements are proven in the kernel, and smarter structural inference rules are introduced with functions akin to tactics. This allows the implementation to cleanly define the typing judgement while also supporting sophisticated inference steps on the input source and fully verifying the type checker's output.

We can setup type checkers on a core language as the primitive implementation of the language, then layer a parser on top. The expressions aren't actually getting parsed: Instead, the implementation treats the source code as a serialization format for the typing derivations it can verify in the kernel
This has been written about before, too. Ive struggled to get the implementation to have quite the structure I wanted until now. I think I probably was trying too hard to fix the TypedEv and Expr types to be the same.

https://github.com/Plecra/stlc/blob/4e2b78a29678ffe8080c983b465f30fe433de92e/derivations/src/lib.rs#L58-L81
This is effectively your standard check function in a type checker, but it isnt responsible for actual verification so we can be a lot more creative in tweaking it

