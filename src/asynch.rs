//! This modules handles asynchronous interactions with the solver.
//!
//! The related function is [`Solver::async_check_sat_or_unk`].
//!
//! Presently, only asynchronous check-sat-s are supported. The idea is to wrap the whole solver in
//! a new thread, and yield a future of the check-sat result. The new thread starts parsing the
//! output right away, which is going to block it. Once it's done, it sends a message to its parent
//! thread with the result.
//!
//! This module uses unsafe code so that the wrapper retains the `&mut solver` (for lifetimes), but
//! the background thread can read the solver's output. If none of your queries on the wrapper
//! produce a result, *i.e.* the solver is still trying to answer the check-sat, and the wrapper is
//! dropped, the drop action **will wait for the slave thread to produce an answer**. This is
//! because otherwise the background thread would keep on listening to `solver`, making using
//! `solver` after the wrapper is dropped unsafe. On this topic, do read the following remark.
//!
//! > **NB:** when the check *runs forever*, the slave process will keep on waiting for the solver
//! > to answer. If you want to be able to keep using the solver in this case, you should spawn the
//! > solver with the right options to add a timeout. For Z3, `-t:500` for a (soft, per query)
//! > timeout, which makes it report `unknown`. This is what the examples below do.
//! >
//! > This is why [`Solver::async_check_sat_or_unk`] is marked `unsafe`: if not careful, one can end
//! > up with a background process burning 100% CPU.
//!
//! # Examples
//!
//! These examples use the second SMT-LIB script from this [stack overflow question] as a script
//! that Z3 struggles with.
//!
//! ```rust
//! fn do_smt_stuff() -> rsmt2::SmtRes<()> {
//!     use std::io::Write;
//!     let parser = () ;
//!     use rsmt2::SmtConf ;
//!
//!     let mut conf = SmtConf::default_z3();
//!     // Setting a timeout because our query will run "forever" otherwise.
//!     conf.option("-t:100");
//!
//!     let mut solver = conf.spawn(parser)? ;
//!
//!     writeln!(solver, r#"
//!         (declare-fun f (Real) Real)
//!         (assert (forall ((a Real) (b Real)) (
//!           = (+ (f a) (f b)) (f (+ a b))
//!         )))
//!         (assert (= (f 2) 4))
//!     "#)?;
//!
//!     { // The following mut-borrows `solver`, this scope lets us use `solver` again afterwards.
//!
//!         let future = unsafe { solver.async_check_sat_or_unk() };
//!
//!         // Non-blocking.
//!         let maybe_result = future.try_get();
//!         assert!(maybe_result.is_none());
//!
//!         // Blocking with timeout.
//!         let maybe_result = future.timeout_get(std::time::Duration::new(0, 50));
//!         assert!(maybe_result.is_none());
//!
//!         // Blocking.
//!         let result = future.get();
//!         assert!(result.expect("reached timeout").is_none());
//!     }
//!
//!     // We can re-use the solver now.
//!     let result = solver.check_sat_or_unk();
//!     assert!(result.expect("reached timeout").is_none());
//!
//!     Ok(())
//! }
//! do_smt_stuff().unwrap()
//! ```
//!
//! [stack overflow question]: https://stackoverflow.com/questions/43246090

use std::{
    sync::mpsc::{channel, Receiver, RecvError, RecvTimeoutError, Sender, TryRecvError},
    time::Duration,
};

use crate::{errors::*, solver::Solver};

/// Messages sent by the slave thread.
type AsyncMsg = SmtRes<Option<bool>>;

/// Send channel for the slave thread.
type AsyncSend = Sender<AsyncMsg>;

/// Receive channel for the master thread.
type AsyncRecv = Receiver<AsyncMsg>;

/// Solver container for (unsafe) mutable reference sharing.
struct Container<Parser> {
    inner: *mut Solver<Parser>,
}
unsafe impl<Parser: Send> Send for Container<Parser> {}

/// Master thread.
#[must_use]
pub struct CheckSatFuture<'sref, Parser> {
    /// Channel for receiving messages from the slave thread.
    recv: AsyncRecv,
    /// Reference to the solver.
    solver: &'sref mut Solver<Parser>,
}
impl<'sref, Parser> Drop for CheckSatFuture<'sref, Parser> {
    fn drop(&mut self) {
        let _ = self.recv.recv();
        ()
    }
}
impl<'sref, Parser: Send + 'static> CheckSatFuture<'sref, Parser> {
    /// Constructor.
    pub fn new(solver: &'sref mut Solver<Parser>) -> Self {
        let (send, recv): (AsyncSend, AsyncRecv) = channel();
        let slf = CheckSatFuture { recv, solver };
        let solver = Container {
            inner: slf.solver as *mut Solver<Parser>,
        };
        std::thread::spawn(move || {
            let solver = unsafe { &mut *solver.inner };
            let result = solver.check_sat_or_unk();
            send.send(result)
        });
        slf
    }

    fn disconnected<T>() -> SmtRes<T> {
        bail!("error during asynchronous check-sat: disconnected from slave thread")
    }

    /// Retrieves the result of the check-sat. Blocking.
    pub fn get(&self) -> SmtRes<Option<bool>> {
        match self.recv.recv() {
            Ok(result) => result,
            Err(RecvError) => Self::disconnected(),
        }
    }

    /// Tries to retrieve the result of the check-sat. Non-blocking.
    pub fn try_get(&self) -> Option<SmtRes<Option<bool>>> {
        match self.recv.try_recv() {
            Ok(result) => Some(result),
            Err(TryRecvError::Empty) => None,
            Err(TryRecvError::Disconnected) => Some(Self::disconnected()),
        }
    }

    /// Tries to retrieve the result of the check-sat with a timeout.
    pub fn timeout_get(&self, timeout: Duration) -> Option<SmtRes<Option<bool>>> {
        match self.recv.recv_timeout(timeout) {
            Ok(result) => Some(result),
            Err(RecvTimeoutError::Timeout) => None,
            Err(RecvTimeoutError::Disconnected) => Some(Self::disconnected()),
        }
    }
}
