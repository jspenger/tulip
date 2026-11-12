Require Import Classical.
Require Import tulip.tla.TLA.
Require Import tulip.tla.lib.LL94_2.

#[local] Open Scope tla_scope.

Section ll94_2.

Context {State : Type}.
#[local] Notation prop := (property State).

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated `Not from ref`):         *)
(* [1]                                                                        *)
(* > Leslie Lamport. 1994. The temporal logic of actions. ACM Trans. Program. *)
(* > Lang. Syst. 16, 3 (May 1994), 872-923.                                   *)
(* > https://doi.org/10.1145/177492.177726                                    *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Additional Rules                                                           *)
(* ========================================================================== *)

(* These rules are presumably only provable using `Classical` *)

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
(* TODO *) Admitted.

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
(* TODO *) Admitted.

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
(* TODO *) Admitted.

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
(* TODO *) Admitted.

End ll94_2.

(* ========================================================================== *)
(* Temporal Quantification                                                    *)
(* ========================================================================== *)

(* See `State` def in tulip.tla.lib.LL94_2 *)
#[local] Definition State (Id Var : Type) : Type := Id -> Var.

(* Not from refs *)
Lemma FF4 {Id Var : Type} (x : Id) (F G : property (State Id Var)) :
    valid (F \impl \AA x : F) -> (* x not free in F *)
        valid ((\AA x : (F \lor G))
            \equiv (F \lor (\AA x : G))).
Proof.
(* TODO *) Admitted.
