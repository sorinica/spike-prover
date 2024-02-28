closure.vo closure.glob closure.v.beautified: closure.v TransClosure.vo
closure.vio: closure.v TransClosure.vio
decidable_set.vo decidable_set.glob decidable_set.v.beautified: decidable_set.v
decidable_set.vio: decidable_set.v
ordered_set.vo ordered_set.glob ordered_set.v.beautified: ordered_set.v
ordered_set.vio: ordered_set.v
TransClosure.vo TransClosure.glob TransClosure.v.beautified: TransClosure.v
TransClosure.vio: TransClosure.v
dickson.vo dickson.glob dickson.v.beautified: dickson.v more_list.vo list_permut.vo ordered_set.vo closure.vo
dickson.vio: dickson.v more_list.vio list_permut.vio ordered_set.vio closure.vio
equiv_list.vo equiv_list.glob equiv_list.v.beautified: equiv_list.v
equiv_list.vio: equiv_list.v
list_permut.vo list_permut.glob list_permut.v.beautified: list_permut.v more_list.vo equiv_list.vo decidable_set.vo
list_permut.vio: list_permut.v more_list.vio equiv_list.vio decidable_set.vio
list_set.vo list_set.glob list_set.v.beautified: list_set.v decidable_set.vo more_list.vo list_permut.vo
list_set.vio: list_set.v decidable_set.vio more_list.vio list_permut.vio
more_list.vo more_list.glob more_list.v.beautified: more_list.v closure.vo
more_list.vio: more_list.v closure.vio
term.vo term.glob term.v.beautified: term.v closure.vo more_list.vo list_permut.vo list_set.vo decidable_set.vo term_spec.vo
term.vio: term.v closure.vio more_list.vio list_permut.vio list_set.vio decidable_set.vio term_spec.vio
term_spec.vo term_spec.glob term_spec.v.beautified: term_spec.v closure.vo more_list.vo list_permut.vo list_set.vo decidable_set.vo
term_spec.vio: term_spec.v closure.vio more_list.vio list_permut.vio list_set.vio decidable_set.vio
rpo.vo rpo.glob rpo.v.beautified: rpo.v closure.vo more_list.vo equiv_list.vo list_permut.vo dickson.vo term_spec.vo term.vo decidable_set.vo ordered_set.vo
rpo.vio: rpo.v closure.vio more_list.vio equiv_list.vio list_permut.vio dickson.vio term_spec.vio term.vio decidable_set.vio ordered_set.vio
