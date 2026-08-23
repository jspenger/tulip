Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

Section rules.

Context {State : Type}.
#[local] Notation prop := (property State).

(* ========================================================================== *)
(* Composition                                                                *)
(* ========================================================================== *)

(* Acyclic composition of `A` and `B` where `A` depends on the specification 
   of `B` (and not the implementation of `B`). *)
(* Note: not from references *)
Lemma COM1 (A_i A_s B_i B_s : prop) :
    valid (A_i \impl A_s)
        -> valid ((A_s \land B_i) \impl B_s)
            -> valid ((A_i \land B_i) \impl (A_s \land B_s)).
Proof.
    admit.
Admitted.

End rules.
