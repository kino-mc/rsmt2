#![doc = r#"Activation literal type and helpers.

For an explanation of what activation literal are, see
[the discussion below][why actlits].

**NB**: while `rmst2`'s actlit API declares some constant symbols in the
underlying solver, these will not appear in the result of
[`get_model`](get_model).


# Relevant functions on solvers

- [`get_actlit`](../trait.Solver.html#method.get_actlit)
- [`get_sactlit`](../trait.Solver.html#method.get_sactlit)
- [`de_actlit`](../trait.Solver.html#method.de_actlit)
- [`set_actlit`](../trait.Solver.html#method.set_actlit)
- [`assert_act`](../trait.Solver.html#method.assert_act)
- [`assert_act_u`](../trait.Solver.html#method.assert_act_u)
- [`print_check_sat_act`](../trait.Solver.html#method.print_check_sat_act)
- [`check_sat_act`](../trait.Solver.html#method.check_sat_act)
- [`check_sat_act_or_unknown`](../trait.Solver.html#method.check_sat_act_or_unknown)



# Usage

First, note that one can create activation literals by hand, and use them in
`check-sat`s with [`check_sat_assuming`][check sat ass]:

```
use rsmt2::* ;

let mut kid = match Kid::default() {
  Ok(kid) => kid,
  Err(e) => panic!("Could not spawn solver kid: {:?}", e)
} ;

{
  let mut solver = solver(& mut kid, ()).unwrap() ;
  solver.declare_const_u("x", "Int").unwrap() ;

  solver.declare_const_u("actlit", "Bool").unwrap() ;
  solver.assert_u("\
    (=> actlit \
        (and (> x 0) (< x 3) (= (mod x 3) 0))\
    )\
  ").unwrap() ;
  assert!{
    ! solver.check_sat_assuming_u( Some("actlit") ).unwrap()
  }
  solver.assert_u("(not actlit)").unwrap() ;

  solver.declare_const_u("other_actlit", "Bool").unwrap() ;
  solver.assert_u("\
    (=> other_actlit \
        (and (> x 7) (= (mod x 2) 0))\
    )\
  ").unwrap() ;
  assert!{
    solver.check_sat_assuming_u( Some("other_actlit") ).unwrap()
  }
  solver.assert_u("(not other_actlit)").unwrap() ;
}

kid.kill().unwrap()
```

The activation literal API makes this process more straightforward:

```
use rsmt2::* ;

let mut kid = match Kid::default() {
  Ok(kid) => kid,
  Err(e) => panic!("Could not spawn solver kid: {:?}", e)
} ;

{
  let mut solver = solver(& mut kid, ()).unwrap() ;
  solver.declare_const_u("x", "Int").unwrap() ;

  let actlit = solver.get_actlit().unwrap() ;
  solver.assert_act_u(& actlit, "(> x 0)").unwrap() ;
  solver.assert_act_u(& actlit, "(< x 3)").unwrap() ;
  solver.assert_act_u(& actlit, "(= (mod x 3) 0)").unwrap() ;

  assert!{
    ! solver.check_sat_act( Some(& actlit) ).unwrap()
  }
  solver.de_actlit(actlit).unwrap() ;
  // At this point `actlit` has been consumed. So it's a bit safer than the
  // version above, since use-after-deactivate is not possible.

  let actlit = solver.get_actlit().unwrap() ;
  solver.assert_act_u(& actlit, "(> x 7)").unwrap() ;
  assert!{
    solver.check_sat_act( Some(& actlit) ).unwrap()
  }
  solver.de_actlit(actlit).unwrap()
}

kid.kill().unwrap()
```





# Discussion on activation literals

The activation literal technique is a much more efficient alternative to the
`push`/`pop` SMT-LIB commands. When a `pop` command is issued, solvers usually
reset themselves and re-declare/assert whatever was before the last push.

Activation literals are boolean nullary symbols controlling the activation of
some assertions.

For instance

```smt
(declare-fun x () Int)

(push 1)
  (assert (> x 0))
  (assert (< x 3))
  (assert (= (mod x 3) 0))
  (check-sat)
  ; unsat
(pop 1)

(push 1)
  (assert (> x 7))
  (assert (= (mod x 2) 0))
  (check-sat)
  (get-value (x))
(pop 1)
```

can be encoded with activation literals as

```smt
(declare-fun x () Int)

(declare-fun actlit_1 () Bool)
(declare-fun actlit_2 () Bool)

(assert (=> actlit_1 (> x 0)) )
(assert (=> actlit_2 (< x 3)) )
(assert (=> actlit_2 (= (mod x 3) 0)) )
(check-sat actlit_1 actlit_2) ; <--- Conditional check-sat
                              ;      usually called "check-sat-assuming"
; unsat

(assert (not actlit_2)) ; <--- Actlit deactivation
                        ;      all its assertions basically disappear

(declare-fun actlit_3 () Bool)

(assert (=> actlit_3 (> x 7)) )
(assert (=> actlit_3 (= (mod x 2) 0)) )
(check-sat actlit_1 actlit_3)
; sat
(get-value (x))
```

This is much more efficient than `push`/`pop`: the conditional `check-sat`s
basically force the activation literals directly in the SAT part of the SMT
solver. Long story short, this means everything the solver learns during the
checks is still valid afterwards. Conversely, after a `pop` solvers are
usually unable to decide what to keep from the checks before the `pop`, and
thus drop everything.

[why actlits]: #discussion-on-activation-literals (Activation literals, why?)
[SActlit]: struct.SActlit.html (SActlit documentation)
[Actlit]: struct.Actlit.html (Actlit documentation)
[phantom]: https://doc.rust-lang.org/std/marker/struct.PhantomData.html (PhantomData documentation)
[check sat ass]: ../trait.Solver.html#method.check_sat_assuming (check_sat_assuming function)
[get_model]: ../trait.Solver.html#method.get_model (get_model function)

"#]

pub use solver::Actlit ;