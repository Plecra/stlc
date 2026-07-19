fn main() {
    let (a, errors) = parser::parse(&mut &b"\\x : A. x"[..]);
    let p = derivations::verify(&a, &mut derivations::ContextIndex::new([].into_iter())).unwrap();
    println!("{a:?} {:?}", p);
    println!("Hello, world!");
}
