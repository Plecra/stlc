#[test]
fn examples() {
    let (a, errors) = parser::parse(&mut &b"\\x : A. x"[..]);
    let p = derivations::verify(&a, &mut derivations::ContextIndex::new([("A".into(), kernel::Bound::TypeVar)].into_iter()).unwrap()).unwrap();
    assert!(errors.is_empty());
    assert_eq!(format!("{a:?}"), r#"Abs("x", Var("A"), Var("x"))"#);
    assert_eq!(format!("{p:?}"), r#"Proof(Typed { context: [("A", TypeVar)], expr: Abs("x", Var("x")), ty: Arrow(Var("A"), Var("A")) })"#);
    let (a, errors) = parser::parse(&mut &b"
        \\toString : Int -> String. \\add : Int -> Int -> Int. \\n : Int. \\m : Int. toString (add n m)
    "[..]);
    let p = derivations::verify(&a, &mut derivations::ContextIndex::new([("Int".into(), kernel::Bound::TypeVar), ("String".into(), kernel::Bound::TypeVar)].into_iter()).unwrap()).unwrap();
    assert!(errors.is_empty());
    assert_eq!(format!("{a:?}"), r#"Abs("toString", Arrow(Var("Int"), Var("String")), Abs("add", Arrow(Var("Int"), Arrow(Var("Int"), Var("Int"))), Abs("n", Var("Int"), Abs("m", Var("Int"), App(Var("toString"), App(App(Var("add"), Var("n")), Var("m")))))))"#);
    assert_eq!(format!("{p:?}"),
        concat!("Proof(Typed { context: [(\"Int\", TypeVar), (\"String\", TypeVar)], ",
            r#"expr: Abs("toString", Abs("add", Abs("n", Abs("m", App(Var("toString"), App(App(Var("add"), Var("n")), Var("m"))))))), "#,
            r#"ty: Arrow(Arrow(Var("Int"), Var("String")), Arrow(Arrow(Var("Int"), Arrow(Var("Int"), Var("Int"))), Arrow(Var("Int"), Arrow(Var("Int"), Var("String"))))) "#,
        "})"));
    let (a, errors) = parser::parse(&mut &b"\\x : A. \\y : B. x y"[..]);
    let _ = derivations::verify(&a, &mut derivations::ContextIndex::new([("A".into(), kernel::Bound::TypeVar), ("B".into(), kernel::Bound::TypeVar)].into_iter()).unwrap()).unwrap_err();
    assert!(errors.is_empty());
    assert_eq!(format!("{a:?}"), r#"Abs("x", Var("A"), Abs("y", Var("B"), App(Var("x"), Var("y"))))"#);
}
