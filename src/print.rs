//! Traits your types must implement so that rsmt2 can use them.
//!
//! Most of the `...2Smt` traits take some notion of information. This lets you change how printing
//! behaves by passing some *print-time info* to commands like
//! [`Solver::assert`].
//!
//! > Technical note: this can be useful to avoid duplicating expressions, for instance if you are
//! > doing `k`-induction and don't want to actually build an expression each time you want to
//! > assert the transition relation with variables distinct from previous ones. Instead, you can
//! > just pass the `k` as print-info and print variables differently based on that.

use std::io;

pub use crate::{errors::*, prelude::*};

/// Type of a model.
pub type Model<Ident, Type, Value> = Vec<(Ident, Vec<(Ident, Type)>, Type, Value)>;

/// A symbol printable in the SMT Lib 2 standard given some info.
pub trait Sym2Smt<Info = ()> {
    /// Prints a symbol to a writer given some info.
    fn sym_to_smt2<Writer>(&self, w: &mut Writer, i: Info) -> SmtRes<()>
    where
        Writer: io::Write;
}

/// An expression printable in the SMT Lib 2 standard given some info.
pub trait Expr2Smt<Info = ()> {
    /// Prints an expression to a writer given some info.
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, i: Info) -> SmtRes<()>
    where
        Writer: io::Write;

    /// Gives a name to an expression (owned version).
    fn to_smt_named<Sym>(self, name: Sym) -> NamedExpr<Sym, Self, Info>
    where
        Sym: Sym2Smt,
        Self: Sized,
    {
        NamedExpr::new(name, self)
    }
    /// Gives a name to an expression (borrowed version).
    fn as_smt_named<Sym>(&self, name: Sym) -> NamedExpr<Sym, &Self, Info>
    where
        Sym: Sym2Smt,
        Self: Sized,
    {
        NamedExpr::new(name, &self)
    }
}

/// A sort printable in the SMT Lib 2 standard.
pub trait Sort2Smt {
    /// Prints a sort to a writer info.
    fn sort_to_smt2<Writer>(&self, w: &mut Writer) -> SmtRes<()>
    where
        Writer: io::Write;
}

/// A symbol and a sort, implemented by by symbol/sort pairs.
///
/// Implement this trait if you want to use your own data structures in solver functions working on
/// lists of sorted symbols. For example, [Solver::define_fun] and [Solver::define_funs_rec_with].
pub trait SymAndSort<Info = ()> {
    /// Type of the symbol.
    type Sym: Sym2Smt<Info>;
    /// Type of the sort.
    type Sort: Sort2Smt;
    /// Symbol accessor.
    fn sym(&self) -> &Self::Sym;
    /// Sort accessor.
    fn sort(&self) -> &Self::Sort;
}
impl<'a, T, Info> SymAndSort<Info> for &'a T
where
    T: SymAndSort<Info>,
{
    type Sym = <T as SymAndSort<Info>>::Sym;
    type Sort = <T as SymAndSort<Info>>::Sort;
    fn sym(&self) -> &Self::Sym {
        (*self).sym()
    }
    fn sort(&self) -> &Self::Sort {
        (*self).sort()
    }
}
impl<Info, Sym, Sort> SymAndSort<Info> for (Sym, Sort)
where
    Sym: Sym2Smt<Info>,
    Sort: Sort2Smt,
{
    type Sym = Sym;
    type Sort = Sort;
    fn sym(&self) -> &Sym {
        &self.0
    }
    fn sort(&self) -> &Sort {
        &self.1
    }
}

/// Function definition data.
///
/// Used by [`Solver::define_funs_rec`] and [`Solver::define_funs_rec`].
pub trait FunDef<Info = ()> {
    /// Type of the function's symbol (name).
    type FunSym: Sym2Smt<Info>;
    /// Type of the arguments (name, sort).
    type SortedSym: SymAndSort<Info>;
    /// Type of the iterator over the arguments.
    type ArgsIter: Iterator<Item = Self::SortedSym>;
    /// Type of the function's output sort.
    type OutSort: Sort2Smt;
    /// Type of the body.
    type Body: Expr2Smt<Info>;

    /// Function name accessor.
    fn fun_sym(&self) -> &Self::FunSym;
    /// Arguments accessor.
    fn args(&self) -> Self::ArgsIter;
    /// Output sort accessor.
    fn out_sort(&self) -> &Self::OutSort;
    /// Function's body accessor.
    fn body(&self) -> &Self::Body;
}
impl<'a, T, Info> FunDef<Info> for &'a T
where
    T: FunDef<Info>,
{
    type FunSym = T::FunSym;
    type SortedSym = T::SortedSym;
    type ArgsIter = T::ArgsIter;
    type OutSort = T::OutSort;
    type Body = T::Body;

    fn fun_sym(&self) -> &Self::FunSym {
        (*self).fun_sym()
    }

    fn args(&self) -> Self::ArgsIter {
        (*self).args()
    }

    fn out_sort(&self) -> &Self::OutSort {
        (*self).out_sort()
    }

    fn body(&self) -> &Self::Body {
        (*self).body()
    }
}
impl<FunSym, SortedSym, Args, OutSort, Body, Info> FunDef<Info> for (FunSym, Args, OutSort, Body)
where
    FunSym: Sym2Smt<Info>,
    SortedSym: SymAndSort<Info>,
    Args: IntoIterator<Item = SortedSym> + Clone,
    OutSort: Sort2Smt,
    Body: Expr2Smt<Info>,
{
    type FunSym = FunSym;
    type SortedSym = SortedSym;
    type ArgsIter = Args::IntoIter;
    type OutSort = OutSort;
    type Body = Body;

    fn fun_sym(&self) -> &FunSym {
        &self.0
    }
    fn args(&self) -> Self::ArgsIter {
        self.1.clone().into_iter()
    }
    fn out_sort(&self) -> &OutSort {
        &self.2
    }
    fn body(&self) -> &Body {
        &self.3
    }
}

/// Contains data for a field of a variant of an ADT.
///
/// - Used by [`AdtVariant`].
/// - `T: AdtVariantField` ⇒ `&T: AdtVariantField`
///
/// Implementing this trait for you own types is totally fine but if you don't, you can
/// use pairs `(impl Sym2Smt, impl Sort2Smt)` which implement this trait. See examples.
///
/// # Examples
///
/// ```rust
/// use rsmt2::print::*;
///
/// let field = ("impl Sym2Smt", "impl Sort2Smt");
/// let _ = field.field_sym();
/// let _ = field.field_sort();
///
/// fn test(_: impl AdtVariantField) {}
/// test(&field);
/// test(field);
/// ```
pub trait AdtVariantField {
    /// Field symbol (name).
    type FieldSym: Sym2Smt;
    /// Field sort.
    type FieldSort: Sort2Smt;
    /// Field symbol accessor.
    fn field_sym(&self) -> &Self::FieldSym;
    /// Field sort accessor.
    fn field_sort(&self) -> &Self::FieldSort;
}
impl<'a, T> AdtVariantField for &'a T
where
    T: AdtVariantField,
{
    type FieldSym = T::FieldSym;
    type FieldSort = T::FieldSort;
    fn field_sym(&self) -> &Self::FieldSym {
        (*self).field_sym()
    }
    fn field_sort(&self) -> &Self::FieldSort {
        (*self).field_sort()
    }
}
impl<FieldSym, FieldSort> AdtVariantField for (FieldSym, FieldSort)
where
    FieldSym: Sym2Smt,
    FieldSort: Sort2Smt,
{
    type FieldSym = FieldSym;
    type FieldSort = FieldSort;

    fn field_sym(&self) -> &FieldSym {
        &self.0
    }
    fn field_sort(&self) -> &FieldSort {
        &self.1
    }
}

/// Stores data for a variant of an ADT.
///
/// - Used by [`AdtDecl`].
/// - `T: AdtVariant` ⇒ `&T: AdtVariant`
///
/// Implementing this trait for you own types is totally fine but if you don't, you can use pairs
/// `(impl Sym2Smt, impl IntoIterator<Item: AdtVariantField>)` which implement this trait. See
/// examples.
///
/// # Examples
///
/// ```rust
/// use rsmt2::print::*;
///
/// let field = ("impl Sym2Smt", "impl Sort2Smt");
/// let fields = vec![field];
/// let variant = ("impl Sym2Smt", &fields);
///
/// fn test(_: impl AdtVariant) {}
/// test(&variant);
/// test(variant);
/// ```
pub trait AdtVariant {
    /// Variant symbol (name).
    type VariantSym: Sym2Smt;
    /// Type of the variant's fields.
    type Field: AdtVariantField;
    /// Iterator over the variant's fields.
    type FieldIter: Iterator<Item = Self::Field>;

    /// Variant symbol accessor.
    fn sym(&self) -> &Self::VariantSym;
    /// Variant fields accessor.
    fn fields(&self) -> Self::FieldIter;
}
impl<'a, T> AdtVariant for &'a T
where
    T: AdtVariant,
{
    type VariantSym = T::VariantSym;
    type Field = T::Field;
    type FieldIter = T::FieldIter;

    fn sym(&self) -> &Self::VariantSym {
        (*self).sym()
    }
    fn fields(&self) -> Self::FieldIter {
        (*self).fields()
    }
}
impl<VariantSym, Field, FieldIntoIter> AdtVariant for (VariantSym, FieldIntoIter)
where
    VariantSym: Sym2Smt,
    Field: AdtVariantField,
    FieldIntoIter: IntoIterator<Item = Field> + Clone,
{
    type VariantSym = VariantSym;
    type Field = Field;
    type FieldIter = FieldIntoIter::IntoIter;

    fn sym(&self) -> &VariantSym {
        &self.0
    }
    fn fields(&self) -> Self::FieldIter {
        self.1.clone().into_iter()
    }
}

/// Gathers data for an ADT declaration.
///
/// - Used by [`Solver::declare_datatypes`].
/// - `T: AdtDecl` ⇒ `&T: AdtDecl`
///
/// Implementing this trait for you own types is totally fine but if you don't, you can use triplets
/// `(impl Sym2Smt, impl IntoIterator<Item: Sort2Smt>, impl IntoIterator<Item: AdtVariant>)` which
/// implement this trait. The second type (sort parameter iterator) must also implement
/// [`ExactSizeIterator`] to access the ADT's arity easily.
///
/// # Examples
///
/// ```rust
/// use rsmt2::print::*;
///
/// let cons_head_field = ("head", "T");
/// let cons_tail_field = ("tail", "(List T)");
/// // Could use any iterable collection here.
/// let cons_fields = vec![cons_head_field, cons_tail_field];
/// let cons_variant = ("cons", &cons_fields);
///
/// // Could use any iterable collection here.
/// let nil_fields = vec![];
/// let nil_variant = ("nil", &nil_fields);
///
/// // Could use any iterable collection here.
/// let variants = [cons_variant, nil_variant];
/// // Could use any exact-size-iterable collection here.
/// let sort_args = ["T"];
///
/// let list_adt = ("List", &sort_args, &variants);
///
/// fn test(_: impl AdtDecl) {}
/// test(&list_adt);
/// test(list_adt);
/// ```
pub trait AdtDecl {
    /// ADT symbol (name).
    type AdtSym: Sym2Smt;
    /// Type of the symbols (names) of the variants (if any).
    type VariantSym: Sym2Smt;

    /// Sort arguments of the ADT.
    type SortArg: Sym2Smt;
    /// Iterator over the sort arguments.
    ///
    /// [`ExactSizeIterator`] because this is how we retrieve the ADT's arity (number of sort
    /// arguments).
    type SortArgsIter: Iterator<Item = Self::SortArg> + ExactSizeIterator;

    /// Type of the ADT's variants.
    type Variant: AdtVariant;
    /// Iterator over the ADT variants.
    type VariantIter: Iterator<Item = Self::Variant>;

    /// ADT symbol accessor.
    fn adt_sym(&self) -> &Self::AdtSym;
    /// ADT sort parameters accessor.
    fn adt_sort_args(&self) -> Self::SortArgsIter;
    /// ADT arity.
    ///
    /// Same as `self.adt_sort_args().len()` (actually defined that way).
    fn arity(&self) -> usize {
        self.adt_sort_args().len()
    }
    /// ADT variants accessor.
    fn adt_variants(&self) -> Self::VariantIter;
}
impl<AdtSym, ArgsIntoIter, VariantIntoIter> AdtDecl for (AdtSym, ArgsIntoIter, VariantIntoIter)
where
    AdtSym: Sym2Smt,
    ArgsIntoIter: IntoIterator + Clone,
    ArgsIntoIter::IntoIter: ExactSizeIterator,
    ArgsIntoIter::Item: Sym2Smt,
    VariantIntoIter: IntoIterator + Clone,
    VariantIntoIter::Item: AdtVariant,
{
    type AdtSym = AdtSym;
    type VariantSym = ArgsIntoIter::Item;

    type SortArg = ArgsIntoIter::Item;
    type SortArgsIter = ArgsIntoIter::IntoIter;

    type Variant = VariantIntoIter::Item;
    type VariantIter = VariantIntoIter::IntoIter;

    fn adt_sym(&self) -> &AdtSym {
        &self.0
    }
    fn adt_sort_args(&self) -> ArgsIntoIter::IntoIter {
        self.1.clone().into_iter()
    }
    fn adt_variants(&self) -> VariantIntoIter::IntoIter {
        self.2.clone().into_iter()
    }
}
impl<'a, T> AdtDecl for &'a T
where
    T: AdtDecl,
{
    type AdtSym = T::AdtSym;
    type VariantSym = T::VariantSym;
    type SortArg = T::SortArg;

    type SortArgsIter = T::SortArgsIter;

    type Variant = T::Variant;
    type VariantIter = T::VariantIter;

    fn adt_sym(&self) -> &Self::AdtSym {
        (*self).adt_sym()
    }
    fn adt_sort_args(&self) -> Self::SortArgsIter {
        (*self).adt_sort_args()
    }
    fn adt_variants(&self) -> Self::VariantIter {
        (*self).adt_variants()
    }
}

/// Writes a string.
#[inline]
pub fn write_str<W: io::Write>(w: &mut W, s: &str) -> SmtRes<()> {
    w.write_all(s.as_bytes())?;
    Ok(())
}

impl<'a, T, Info> Sym2Smt<Info> for &'a T
where
    T: Sym2Smt<Info> + ?Sized,
{
    fn sym_to_smt2<Writer>(&self, writer: &mut Writer, info: Info) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        (*self).sym_to_smt2(writer, info)
    }
}

impl<'a, T, Info> Expr2Smt<Info> for &'a T
where
    T: Expr2Smt<Info> + ?Sized,
{
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, info: Info) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        (*self).expr_to_smt2(writer, info)
    }
}

impl<'a, T> Sort2Smt for &'a T
where
    T: Sort2Smt + ?Sized,
{
    fn sort_to_smt2<Writer>(&self, writer: &mut Writer) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        (*self).sort_to_smt2(writer)
    }
}

impl<T> Sym2Smt<T> for str {
    fn sym_to_smt2<Writer>(&self, writer: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}
impl<T> Expr2Smt<T> for str {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}
impl Sort2Smt for str {
    fn sort_to_smt2<Writer>(&self, writer: &mut Writer) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}

impl<T> Sym2Smt<T> for String {
    fn sym_to_smt2<Writer>(&self, writer: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}
impl<T> Expr2Smt<T> for String {
    fn expr_to_smt2<Writer>(&self, writer: &mut Writer, _: T) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}
impl Sort2Smt for String {
    fn sort_to_smt2<Writer>(&self, writer: &mut Writer) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write_str(writer, self)
    }
}

/// Wraps an expression and a symbol. Symbol is understood as the name of the expression.
///
/// ```rust
/// use rsmt2::prelude::*;
/// let mut conf = SmtConf::default_z3();
/// conf.unsat_cores();
/// # println!("unsat_cores: {}", conf.get_unsat_cores());
///
/// let mut solver = Solver::new(conf, ()).unwrap();
/// solver.declare_const("n", "Int").unwrap();
/// solver.declare_const("m", "Int").unwrap();
///
/// solver.assert("true").unwrap();
///
/// let e_1 = "(> n 7)";
/// let label_e_1 = "e_1";
/// let named = NamedExpr::new(label_e_1, e_1);
/// solver.assert(&named).unwrap();
///
/// let e_2 = "(and (> m n) (< m 7))";
/// let label_e_2 = "e_2";
/// let named = NamedExpr::new(label_e_2, e_2);
/// solver.assert(&named).unwrap();
///
/// assert!(!solver.check_sat().unwrap());
/// let core: Vec<String> = solver.get_unsat_core().unwrap();
/// assert_eq!(core, vec![label_e_1, label_e_2]);
/// ```
pub struct NamedExpr<Sym, Expr, Info> {
    /// Symbol.
    sym: Sym,
    /// Expression.
    expr: Expr,
    /// Phantom data for `Info`.
    _phantom: std::marker::PhantomData<Info>,
}
impl<Sym, Expr, Info> NamedExpr<Sym, Expr, Info> {
    /// Constructor.
    pub fn new(sym: Sym, expr: Expr) -> Self {
        Self {
            sym,
            expr,
            _phantom: std::marker::PhantomData,
        }
    }
}
impl<Sym, Expr, Info> Expr2Smt<Info> for NamedExpr<Sym, Expr, Info>
where
    Sym: Sym2Smt<()>,
    Expr: Expr2Smt<Info>,
{
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, i: Info) -> SmtRes<()>
    where
        Writer: io::Write,
    {
        write!(w, "(! ")?;
        self.expr.expr_to_smt2(w, i)?;
        write!(w, " :named ")?;
        self.sym.sym_to_smt2(w, ())?;
        write!(w, ")")?;
        Ok(())
    }
}
