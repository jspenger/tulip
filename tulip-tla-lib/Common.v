Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

Section common.

Context {State : Type}.
#[local] Notation prop := (property State).

Lemma util_suffix_0 (beh : behavior State) :
    util_suffix beh 0 = beh.
Proof.
(* TODO *) Admitted.

Lemma util_beh_eq (b c : behavior State) :
    (forall n : nat, b n = c n) ->
        util_stuttering_equivalent b c.
Proof.
(* TODO *) Admitted.

End common.
