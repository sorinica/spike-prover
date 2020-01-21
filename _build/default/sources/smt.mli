val print_smt :
           < has_bit : int -> bool;
             negative_lits : < content : Literals.concrete_literal; .. > list;
             number : int;
             positive_lits : < content : Literals.concrete_literal; .. > list;
             set_bit : int -> unit;
             variables : (int * Symbols.sort * 'a) list; .. > ->
           'b ->
           < negative_lits : < content : Literals.concrete_literal; .. > list;
             positive_lits : < content : Literals.concrete_literal; .. > list;
             variables : (int * Symbols.sort * 'c) list; .. >
           list -> unit
