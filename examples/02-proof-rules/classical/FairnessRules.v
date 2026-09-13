Require Import Classical.
Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

Section rules.

Context {State : Type}.
#[local] Notation prop := (property State).

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated):                        *)
(* > Leslie Lamport. 1994. The temporal logic of actions. ACM Trans. Program. *)
(* > Lang. Syst. 16, 3 (May 1994), 872-923.                                   *)
(* > https://doi.org/10.1145/177492.177726                                    *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Additional Rules                                                           *)
(* ========================================================================== *)

(* Comment: these rules are presumably only provable using classical logic's
   `excluded_middle` *)

Lemma WF1 {V : Type} (P Q N A : prop) (f : State -> V) :
    valid (
        P \land [N]_f \impl (P ' \lor Q ')
    )
    /\ valid(
        P \land <<(N \land A)>>_f \impl Q '
    )
    /\ valid(
        P \impl \enabled <<A>>_f
    )
    -> valid(
        (([]([N]_f)) \land (\wf A \sub f))
        \impl
        (P \leadsto Q)
    ).
Proof.
    admit.
Admitted.

Lemma WF2 {Vf Vg : Type} (N M A B P F : prop) (f : State -> Vf) (g : State -> Vg) :
    valid (
        <<(N \land B)>>_f \impl <<M>>_g
    )
    /\ valid (
        P \land (P ') \land <<(N \land A)>>_f \land \enabled <<M>>_g \impl B
    )
    /\ valid (
        P \land \enabled <<M>>_g \impl \enabled <<A>>_f
    )
    /\ valid (
        ([]([(N \land (\lnot B))]_f)) \land (\wf A \sub f) \land ([]F) \land (<>([](\enabled <<M>>_g))) \impl (<>([]P))
    )
    -> valid (
        (([]([N]_f)) \land (\wf A \sub f) \land ([]F)) \impl (\wf M \sub g)
    ).
Proof.
    admit.
Admitted.

Lemma SF1 {V : Type} (P Q N A F : prop) (f : State -> V) :
    valid(
        (P \land ([N]_f)) \impl ((P ') \lor (Q '))
    )
    /\ valid(
        (P \land (<<(N \land A)>>_f)) \impl (Q ')
    )
    /\ valid(
        (([]P) \land ([]([N]_f)) \land ([]F)) \impl (<>(\enabled (<<A>>_f)))
    )
    -> valid(
        (([]([N]_f)) \land (\sf A \sub f) \land ([]F)) \impl (P \leadsto Q)
    ).
Proof.
    admit.
Admitted.

Lemma SF2 {Vf Vg : Type} (N M A B P F : prop) (f : State -> Vf) (g : State -> Vg) :
    valid (
        (<<(N \land B)>>_f) \impl (<<M>>_g) 
    )
    /\ valid (
        P \land (P ') \land (<<(N \land A)>>_f) \impl B
    )
    /\ valid (
        P \land (\enabled (<<M>>_g)) \impl (\enabled (<<A>>_f))
    )
    /\ valid (
        (([]([(N \land (\lnot B))]_f)) \land (\sf A \sub f) \land ([]F) \land ([]<>(\enabled (<<M>>_g)))) \impl (<>([]P))
    )
    -> valid (
        (([]([N]_f)) \land (\sf A \sub f) \land ([]F)) \impl (\sf M \sub g)
    ).
Proof.
    admit.
Admitted.

End rules.
