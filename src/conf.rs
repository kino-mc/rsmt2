#![ doc = "
Solver configuration, contains backend solver specific info.
"]

/// Solver specific commands and parsing functions.
pub struct SolverConf {
  pub check_sat_assuming: & 'static str,
}

impl SolverConf {
  /// Creates a new z3-like solver configuration.
  pub fn z3() -> Self {
    SolverConf { check_sat_assuming: "check-sat" }
  }
}