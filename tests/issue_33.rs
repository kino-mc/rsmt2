//! https://github.com/kino-mc/rsmt2/issues/33

mod issue_33 {

    #[test]
    fn multiline_sexpr() {
        let input = "(\n\
  (define-fun /0 ((x!0 Real) (x!1 Real)) Real\n\
      (ite (and (= x!0 1.0) (= x!1 (- (/ 3.0 4.0)))) (- (/ 4.0 3.0))\n\
      (ite (and (= x!0 1.0) (= x!1 (/ 3.0 4.0))) (/ 4.0 3.0)\n\
      0.0)))\n\
)";

        let mut parser = rsmt2::parse::SmtParser::new(input.as_bytes());
        match parser.get_model(false, ()) {
            Ok(m) => {
                assert_eq!(m.len(), 1);
                let (id, params, out, body) = &m[0];
                assert_eq!(id, "/0");
                let mut params = params.into_iter();
                assert_eq!(params.next(), Some(&("x!0".into(), "Real".into())));
                assert_eq!(params.next(), Some(&("x!1".into(), "Real".into())));
                assert_eq!(params.next(), None);
                assert_eq!(out, "Real");
                assert_eq!(
                    body,
                    "\
                    (ite (and (= x!0 1.0) (= x!1 (- (/ 3.0 4.0)))) (- (/ 4.0 3.0))\n\
                    (ite (and (= x!0 1.0) (= x!1 (/ 3.0 4.0))) (/ 4.0 3.0)\n\
                    0.0))\
                "
                )
            }
            Err(e) => {
                println!("Error : {:#?}", e);
                panic!("error")
            }
        }
    }

    #[test]
    fn multiline_sexpr_with_comment() {
        let input = "(
  (define-fun x1 () Real
      (/ 1.0 4.0))
  (define-fun x0 () Real
      (/ 1.0 2.0))
  (define-fun /0 ((x!0 Real) (x!1 Real)) Real
      (ite (and (= x!0 1.0) (= x!1 (- (/ 3.0 4.0)))) (- (/ 4.0 3.0))
      (ite (and (= x!0 1.0) (= x!1 (/ 3.0 4.0))) (/ 4.0 3.0) ; a comment
      0.0)))
)";

        let mut parser = rsmt2::parse::SmtParser::new(input.as_bytes());
        match parser.get_model(false, ()) {
            Ok(_) => (),
            Err(e) => {
                println!("Error : {:#?}", e);
                panic!("error")
            }
        }
    }

    #[test]
    fn multiline_sexpr_with_quoted_ident() {
        let input = "(
  (define-fun x1 () Real
      (/ 1.0 4.0))
  (define-fun x0 () Real
      (/ 1.0 2.0))
  (define-fun /0 ((x!0 Real) (x!1 Real)) Real
      (ite (and (= x!0 1.0) (= x!1 (- (/ 3.0 4.0)))) (- (/ 4.0 3.0))
      (ite (and (= x!0 1.0) (= x!1 (/ 3.0 4.0))) (/ 4.0 | some multiline
      ident|)
      0.0)))
)";

        let mut parser = rsmt2::parse::SmtParser::new(input.as_bytes());
        match parser.get_model(false, ()) {
            Ok(_) => (),
            Err(e) => {
                println!("Error : {:#?}", e);
                panic!("error")
            }
        }
    }

    #[test]
    fn just_id() {
        let input = "(
  (define-fun x1 () Real
      x2
  )
)";

        let mut parser = rsmt2::parse::SmtParser::new(input.as_bytes());
        match parser.get_model(false, ()) {
            Ok(_) => (),
            Err(e) => {
                println!("Error : {:#?}", e);
                panic!("error")
            }
        }
    }
}
