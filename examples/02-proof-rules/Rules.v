Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

Section rules.

Context {State : Type}.
#[local] Notation prop := (property State).

(* ========================================================================== *)
(* Utility lemmas (local)                                                     *)
(* ========================================================================== *)

(* Note: not from references *)
#[local] Lemma util_suffix_0 (beh : behavior State) :
    util_suffix beh 0 = beh.
Proof.
  admit.
Admitted.

(* Note: not from references *)
#[local] Lemma util_beh_eq (b c : behavior State) :
    (forall n : nat, b n = c n) ->
        util_stuttering_equivalent b c.
Proof.
  admit.
Admitted.

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated):                        *)
(* > Leslie Lamport. 1994. The temporal logic of actions. ACM Trans. Program. *)
(* > Lang. Syst. 16, 3 (May 1994), 872–923.                                   *)
(* > https://doi.org/10.1145/177492.177726                                    *)
(*                                                                            *)
(* Other references:                                                          *)
(* > Stephan Merz. 2003. On the Logic of TLA+. Computing and Informatics. 22, *)
(* > 3-4 (2003), 351–379.                                                     *)
(* ========================================================================== *)

(* ========================================================================== *)
(* The Rules of Simple Temporal Logic                                         *)
(* ========================================================================== *)

Lemma STL1 (F : prop) :
    valid F ->
        valid ([]F).
Proof.
  admit.
Admitted.

Lemma STL2 (F : prop) :
    valid ([]F \impl F).
Proof.
  admit.
Admitted.

Lemma STL3 (F : prop) :
    util_stuttering_closed F ->
        valid ([][]F \equiv []F).
Proof.
  admit.
Admitted.

Lemma STL4 (F G : prop) :
    valid (F \impl G) ->
        valid ([]F \impl []G).
Proof.
  admit.
Admitted.

(* STL4 (Merz, 2003) *)
Lemma STL4_2 (F G : prop) :
    valid (
        [](F \impl G) \impl
            ([]F \impl []G)).
Proof.
  admit.
Admitted.

Lemma STL5 (F G : prop) :
    valid (
        [](F \land G) \equiv
            []F \land []G
    ).
Proof.
  admit.
Admitted.

Lemma STL6 (F G : prop) :
    (util_stuttering_closed F /\ util_stuttering_closed G) ->
        valid (
            <>[]F \land <>[]G
            \equiv
            <>[](F \land G)
        ).
Proof.
  admit.
Admitted.

Lemma LATTICE (T : Type) (wf_rel : T -> T -> Prop) (F : prop) (H : T -> prop) (G : prop) :
    (util_stuttering_closed G
    /\ (forall c : T, util_stuttering_closed (H c))
    (* The well-founded partial order `wf_rel` is of direction 'less-than'
       whereas Lamport's partial order `\succ` is of direction 'greater-than' *)
    /\ well_founded wf_rel
    /\ valid (
        F \impl (
            \A c \in T :
                H c \leadsto
                    (G \lor (\E d \in T : ((Lift0 (wf_rel d c)) \land (H d))))
        )
    ))
    ->
    valid (F \impl ((\E c : (H c)) \leadsto G)).
Proof.
  admit.
Admitted.

(* Comment: Some of the presented proof rules could be strengthened. This     *)
(* applies to STL4 (for which the strengthened version is STL4_2 (Merz 2003)),*)
(* TLA1, TLA2, INV1, LATTICE, F2. They are currently written in the form      *)
(* `valid A -> valid B`, and could be strengthened to `valid ([]A \impl B)`.  *)
(* Local rule R1 proves that the strengthened form implies the other.         *)

(* Note: not from references *)
#[local] Lemma R1 (F G : prop) :
    valid ([]F \impl G)
        -> valid F
            -> valid G.
Proof.
  admit.
Admitted.

(* Note: not from references *)
#[local] Lemma R2 (F G : prop) :
    valid (F \impl G)
        -> valid F
            -> valid G.
Proof.
  admit.
Admitted.

(* ========================================================================== *)
(* The Basic Rules of TLA                                                     *)
(* ========================================================================== *)

Lemma TLA1 {V : Type} (P : prop) (f : State -> V) :
    util_stuttering_closed P
    ->
    valid (
        (P \land (UNCHANGED f))
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
  admit.
Admitted.

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
  admit.
Admitted.

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
  admit.
Admitted.

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
  admit.
Admitted.

(* ========================================================================== *)
(* Quantification                                                             *)
(* ========================================================================== *)

Lemma F1 {T : Type} (F : T -> prop) (e : T) :
    valid (
        (F e)
        \impl
        (\E c : (F c))
    ).
Proof.
  admit.
Admitted.

Lemma F2 {T : Type} (F : T -> prop) (G : prop) :
    valid (
        (\A c : ((F c) \impl G))
    )
    ->
    valid(
        ((\E c : (F c)) \impl G)
    ).
Proof.
  admit.
Admitted.

(* TODO: E1 *)

(* TODO: E2 *)

End rules.
