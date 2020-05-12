//! A few examples of using rsmt2.

/// Convenience macro.
#[cfg(test)]
macro_rules! smtry {
    ($e:expr, failwith $( $msg:expr ),+) => (
        match $e {
            Ok(something) => something,
            Err(e) => panic!( $($msg),+ , e)
        }
    );
}

pub mod print_time;
pub mod simple;

#[cfg(test)]
fn get_solver<Parser>(p: Parser) -> crate::Solver<Parser> {
    match crate::Solver::default_z3(p) {
        Ok(solver) => solver,
        Err(e) => panic!("Could not spawn solver solver: {:?}", e),
    }
}
