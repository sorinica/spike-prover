class virtual pi_object :
  object
    val mutable is_pi : bool Diverse.pointer
    method virtual compute_pi : bool
    method is_pi : bool
  end
val name_strat_pi : string
