Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

Section ll94.

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
(* The Rules of Simple Temporal Logic                                         *)
(* ========================================================================== *)

Lemma STL1 (F : prop) :
    valid F ->
        valid ([]F).
Proof.
(* TODO *) Admitted.

Lemma STL2 (F : prop) :
    valid ([]F \impl F).
Proof.
(* TODO *) Admitted.

Lemma STL3 (F : prop) :
    util_stuttering_closed F ->
        valid ([][]F \equiv []F).
Proof.
(* TODO *) Admitted.

Lemma STL4 (F G : prop) :
    valid (F \impl G) ->
        valid ([]F \impl []G).
Proof.
(* TODO *) Admitted.

Lemma STL5 (F G : prop) :
    valid (
        [](F \land G) \equiv
            []F \land []G
    ).
Proof.
(* TODO *) Admitted.

Lemma STL6 (F G : prop) :
    (util_stuttering_closed F /\ util_stuttering_closed G) ->
        valid (
            <>[]F \land <>[]G
            \equiv
            <>[](F \land G)
        ).
Proof.
(* TODO *) Admitted.

Lemma LATTICE (T : Type) (wf_rel : T -> T -> Prop) (F : prop) (H : T -> prop) (G : prop) :
    (util_stuttering_closed G
    /\ (forall c : T, util_stuttering_closed (H c))
    (* The well-founded partial order `wf_rel` is of direction 'less-than'
       whereas Lamport's partial order `\succ` is of direction 'greater-than' *)
    /\ well_founded wf_rel
    /\ valid (
        F \impl (
            \A c \in T \st
                H c \leadsto
                    (G \lor (\E d \in T \st ((Lift0 (wf_rel d c)) \land (H d))))
        )
    ))
    ->
    valid (F \impl ((\E c \st (H c)) \leadsto G)).
Proof.
(* TODO *) Admitted.

(* ========================================================================== *)
(* The Basic Rules of TLA                                                     *)
(* ========================================================================== *)

Lemma TLA1 {V : Type} (P : prop) (f : State -> V) :
    util_stuttering_closed P
    ->
    valid (
        (P \land (\unchanged f))
        \impl
        (P ')
    )
    ->
    valid (
        []P
        \equiv
        (P \land []([P \impl P ']_f))
    ).
Proof.
(* TODO *) Admitted.

Lemma TLA2 {Vf Vg : Type} (P A Q B : prop) (f : State -> Vf) (g : State -> Vg) :
    valid (
        (P \land ([A]_f))
        \impl
        (Q \land ([B]_g))
    )
    ->
    valid (
        ([]P \land []([A]_f))
        \impl
        ([]Q \land []([B]_g))
    ).
Proof.
(* TODO *) Admitted.

(* ========================================================================== *)
(* Additional Rules                                                           *)
(* ========================================================================== *)

Lemma INV1 {V : Type} (I N : prop) (f : State -> V) :
    util_stuttering_closed I ->
    valid (
        (I \land ([N]_f))
        \impl
        (I ')
    ) ->
    valid (
        (I \land ([]([N]_f)))
        \impl
        ([]I)
    ).
Proof.
(* TODO *) Admitted.

Lemma INV2 {V : Type} (I N : prop) (f : State -> V) :
    util_stuttering_closed I ->
    valid (
        ([]I)
        \impl
        (
            ([]([N]_f))
            \equiv
            ([]([(N \land I \land I ')]_f))
        )
    ).
Proof.
(* TODO *) Admitted.

(* ========================================================================== *)
(* Quantification                                                             *)
(* ========================================================================== *)

Lemma F1 {T : Type} (F : T -> prop) (e : T) :
    valid (
        (F e)
        \impl
        (\E c \st (F c))
    ).
Proof.
(* TODO *) Admitted.

Lemma F2 {T : Type} (F : T -> prop) (G : prop) :
    valid (
        (\A c \st ((F c) \impl G))
    )
    ->
    valid(
        ((\E c \st (F c)) \impl G)
    ).
Proof.
(* TODO *) Admitted.

End ll94.
