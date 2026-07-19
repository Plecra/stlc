fn main() {
    let (a, errors) = parser::parse(&mut &b"\\x : A. x"[..]);
    let p = derivations::verify(&a, &mut derivations::ContextIndex::new([].into_iter())).unwrap();
    assert!(errors.is_empty());
    assert_eq!(format!("{a:?}"), r#"Abs("x", Base("A"), Var("x"))"#);
    assert_eq!(format!("{p:?}"), r#"Proof(Typed { context: [], expr: Abs("x", Var("x")), ty: Arrow(Base("A"), Base("A")) })"#);
    let (a, errors) = parser::parse(&mut &b"
        \\toString : Int -> String. \\add : Int -> Int -> Int. \\n : Int. \\m : Int. toString (add n m)
    "[..]);
    let p = derivations::verify(&a, &mut derivations::ContextIndex::new([].into_iter())).unwrap();
    assert!(errors.is_empty());
    assert_eq!(format!("{a:?}"), r#"Abs("toString", Arrow(Base("Int"), Base("String")), Abs("add", Arrow(Base("Int"), Arrow(Base("Int"), Base("Int"))), Abs("n", Base("Int"), Abs("m", Base("Int"), App(Var("toString"), App(App(Var("add"), Var("n")), Var("m")))))))"#);
    assert_eq!(format!("{p:?}"),
        concat!("Proof(Typed { context: [], ",
            r#"expr: Abs("toString", Abs("add", Abs("n", Abs("m", App(Var("toString"), App(App(Var("add"), Var("n")), Var("m"))))))), "#,
            r#"ty: Arrow(Arrow(Base("Int"), Base("String")), Arrow(Arrow(Base("Int"), Arrow(Base("Int"), Base("Int"))), Arrow(Base("Int"), Arrow(Base("Int"), Base("String"))))) "#,
        "})"));
}
