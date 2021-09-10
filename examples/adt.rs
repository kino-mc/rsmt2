#[test]
fn test_adt() {
    run()
}

fn run() {
    use rsmt2::{
        print::{AdtDecl, AdtVariant, AdtVariantField},
        Solver,
    };
    let mut solver = Solver::default_z3(()).unwrap();

    // Alright, so we're going to declared two mutually recursive sorts. It is easier to pack the
    // sort-declaration data in custom types. If you want to declare a sort, you most likely
    // already have a representation for it, so working on custom types is reasonable.

    // Notice that the `AdtDecl`, `AdtVariantField` and `AdtVariant` traits from `rsmt2::print::_`
    // are in scope. This is what our custom types will need to generate to declare the sort.

    // We'll use static string slices for simplicity as `&str` implements all printing traits.
    type Sym = &'static str;
    type Sort = &'static str;

    // Let's start with the top-level sort type.
    struct MyAdt {
        // Name of the sort, for instance `List`.
        sym: Sym,
        // Symbol(s) for the type parameter(s), for instance `T` for `List<T>`. Must be a collection
        // of known length, because rsmt2 needs to access the arity (number of type parameters).
        args: Vec<Sym>,
        // Body of the sort: its variants. For instance the `nil` and `cons` variants for `List<T>`.
        variants: Vec<Variant>,
    }
    impl MyAdt {
        // This thing build the actual declaration expected by rsmt2. Its output is something that
        // implements `AdtDecl` and can only live as long as the input ref to `self`.
        fn as_decl<'me>(&'me self) -> impl AdtDecl + 'me {
            // Check out rsmt2's documentation and you'll see that `AdtDecl` is already implemented for
            // certain triplets.
            (
                // Symbol.
                &self.sym,
                // Sized collection of type-parameter symbols.
                &self.args,
                // Variant, collection of iterator over `impl AdtVariant` (see below).
                self.variants.iter().map(Variant::as_decl),
            )
        }

        fn tree() -> Self {
            Self {
                sym: "Tree",
                args: vec!["T"],
                variants: vec![Variant::tree_leaf(), Variant::tree_node()],
            }
        }
    }

    // Next up, variants. A variant is a symbol (*e.g.* `nil` or `cons` for `List<T>`) and some
    // fields which describe the data stored in the variant.
    struct Variant {
        sym: Sym,
        fields: Vec<Field>,
    }
    impl Variant {
        // Variant declaration; again, `AdtVariant` is implemented for certain types of pairs.
        fn as_decl<'me>(&'me self) -> impl AdtVariant + 'me {
            (
                // Symbol.
                self.sym,
                // Iterator over field declarations.
                self.fields.iter().map(Field::as_decl),
            )
        }

        fn tree_leaf() -> Self {
            Self {
                sym: "leaf",
                fields: vec![],
            }
        }
        fn tree_node() -> Self {
            Self {
                sym: "node",
                fields: vec![Field::tree_node_value(), Field::tree_node_children()],
            }
        }
    }

    // A symbol and a sort: describes a piece of data in a variant with a symbol to retrieve it,
    // *i.e.* the name of the field.
    struct Field {
        sym: Sym,
        sort: Sort,
    }
    impl Field {
        // As usual, `AdtVariantField` is implemented for certain pairs.
        fn as_decl(&self) -> impl AdtVariantField {
            (self.sym, self.sort)
        }

        fn tree_node_value() -> Self {
            Self {
                sym: "value",
                sort: "T",
            }
        }
        fn tree_node_children() -> Self {
            Self {
                sym: "children",
                sort: "(TreeList T)",
            }
        }
    }

    let tree = MyAdt::tree();

    // Now this `tree` uses an non-existing `(TreeList T)` sort to store its children, let's declare
    // it now.

    let nil = Variant {
        sym: "nil",
        fields: vec![],
    };
    let cons = Variant {
        sym: "cons",
        fields: vec![
            Field {
                sym: "car",
                sort: "(Tree T)",
            },
            Field {
                sym: "cdr",
                sort: "(TreeList T)",
            },
        ],
    };
    let tree_list = MyAdt {
        sym: "TreeList",
        args: vec!["T"],
        variants: vec![nil, cons],
    };

    println!("declaring ADTs `Tree<T>` and `TreeList<T>`");
    solver
        // These sort are mutually recursive, `Solver::declare_datatypes` needs to declare them at the
        // same time.
        .declare_datatypes(&[tree.as_decl(), tree_list.as_decl()])
        .unwrap();

    // That's it! Solver now knows these sorts and we can use them.

    println!("declaring two `Tree<_>` values");
    solver.declare_const("t1", "(Tree Int)").unwrap();
    solver.declare_const("t2", "(Tree Bool)").unwrap();

    println!("asserting some stuff");
    solver.assert("(> (value t1) 20)").unwrap();
    solver.assert("(not (is-leaf t2))").unwrap();
    solver.assert("(not (value t2))").unwrap();

    println!("check-sat, should be sat");
    let sat = solver.check_sat().unwrap();
    assert!(sat);
    println!("it is!");
}

fn main() {
    run();
    println!("everything is fine");
}
