Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated):                        *)
(* > Leslie Lamport. 2026. A Science of Concurrent Programs. Cambridge        *)
(* > University Press.                                                        *)
(* > https://doi.org/10.1017/9781009719841                                    *)
(*                                                                            *)
(* Other references:                                                          *)
(* > Martin Abadi and Leslie Lamport. 1995. Conjoining Specifications. ACM    *)
(* > Trans. Program. Lang. Syst. 17, 3 (May 1995), 507-535.                   *)
(* > https://doi.org/10.1145/203095.201069                                    *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Utility lemmas (local)                                                     *)
(* ========================================================================== *)

(* Ref: SCP Section 8.2.1.2 *)
(* "F is true of the finite behavior \sigma(0) -> ... -> \sigma(k-1)" *)
(* "For a safety property, true through state k means true if all states i with
   i > k equal state k" *)
(* Note: we define the tts operator by excluding the k'th state unlike SCP that
   includes the k'th state *)
Definition util_tts {State : Type} (P : property State) (beh : behavior State) (k : nat) : Prop :=
    k = 0
    \/ (exists beh' : behavior State,
            P beh'
            /\ (forall n : nat, n < k -> beh' n = beh n)).

(* Ref: "Conjoining Specifications", section 3.4 *)
(* The closure of F `C(F)` is defined "such that a behavior \sigma satisfies
   C(F) iff every prefix of \sigma satisfies F". *)
(* `\C(F)` *)
Definition util_closure {State : Type} (F : property State) : property State :=
    fun beh => forall n : nat, util_tts F beh n.

(* Ref: "Conjoining Specifications", section 3.5 *)
(* The "+ operator" is defined such that "a behavior \sigma satisfies E+v iff
   either \sigma satisfies E, or there is some n such that (1) E holds for the
   first n states of \sigma and (2) v never changes from the (n + 1)st state
   on" *)
(* `F_{+v}` *)
Definition util_plus_operator {State V : Type} (F : property State) (v : State -> V) : property State :=
    fun beh =>
        F beh
        \/ (exists k : nat,
                (forall n : nat, k <= n -> v (beh n) = v (beh (S n)))
                /\ util_tts F beh k).

(* Ref: "Conjoining Specifications", section 3.5 *)
(* The "-+-> operator" is defined such that "E -+-> M is true of a behavior
   \sigma iff E => M is true of \sigma and, for every n >= 0, if E holds for the
   first n states of \sigma, then M holds for the first n + 1 states of
   \sigma." *)
(* `E -+-> F` *)
Definition util_plus_arrow {State : Type} (E F : property State) : property State :=
    fun beh =>
        (E beh -> F beh)
        /\ (forall n : nat,
                util_tts E beh n -> util_tts F beh (S n)).

(* ========================================================================== *)
(* Composition                                                                *)
(* ========================================================================== *)

Section rules.

Context {State : Type}.
#[local] Notation prop := (property State).

(* Ref: SCP Theorem 8.7 (Decomposition Theorem) *)
Theorem Decomposition {V : Type} (v : State -> V) (E Ml M : nat -> prop) :
    (forall i : nat,
            util_stuttering_closed (Ml i))  ->
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j : (util_closure (M j)))
                \impl (E i))) ->
    (* 2. (a) *)
    (forall i : nat,
            valid (((util_plus_operator (util_closure (E i)) v) \land (util_closure (Ml i)))
                \impl (util_closure (M i)))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((Ml i) \land (\A j : ((LIFT0 (j < i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\A i : Ml i)
        \impl (\A i : M i)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
(* Acyclic form of the `Decomposition` theorem with strengthening of hypothesis 
   (1.) by replacing `util_closure (M j)` with `M j` *)
Theorem Decomposition0 (E Ml M : nat -> prop) :
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j : ((LIFT0 (j < i)) \impl (M j)))
                \impl (E i))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((Ml i) \land (\A j : ((LIFT0 (j < i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\A i : Ml i) \impl (\A i : M i)).
Proof.
(* TODO *)  Admitted.

(* Acyclic composition of `M0` and `M1` where `M1` depends on the specification 
   of `M0` (and not the implementation `Ml0` of `M0`). *)
(* Not from refs *)
#[local] Example ex_01 (Ml0 M0 Ml1 M1 : prop) :
    valid (Ml0  \impl  M0)  ->
        valid ((M0 \land Ml1)  \impl  M1)  ->
            valid ((Ml0 \land Ml1)  \impl  (M0 \land M1)).
Proof.
(* TODO *)  Admitted.

(* Ref: SCP Theorem 8.8 (Composition Theorem) *)
Theorem Composition {V : Type} (v : State -> V) (E M : prop) (E_ M_ : nat -> prop) :
    util_stuttering_closed E  ->
    (forall j : nat,
            util_stuttering_closed (M_ j))  ->
    (* If... *)
    (* 1. *)
    valid (\A i : (((util_closure E) \land (\A j : (util_closure (M_ j))))
        \impl (E_ i))) ->
    (* 2. (a) *)
    valid (((util_plus_operator (util_closure E) v) \land (\A j : (util_closure (M_ j))))
        \impl (util_closure M)) ->
    (* 2. (b) *)
    valid ((E \land (\A j : M_ j))
        \impl M) ->
    (* ...then *)
    valid ((\A j : (util_plus_arrow (E_ j) (M_ j)))
        \impl (util_plus_arrow E M)).
Proof.
(* TODO *) Admitted.

(* Ref: "Conjoining Specifications" Corollary 1 *)
Corollary CompositionCor1 {V : Type} (v : State -> V) (E Ml M : prop) :
    util_stuttering_closed E ->
    util_stuttering_closed Ml ->
    (* If... *)
    valid ((util_closure E)
        \impl E)  ->
    (* (a) *)
    valid (((util_plus_operator E v) \land (util_closure Ml))
        \impl (util_closure M)) ->
    (* (b) *)
    valid ((E \land Ml)
        \impl M) ->
    (* ...then *)
    valid ((util_plus_arrow E Ml)
        \impl (util_plus_arrow E M)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
(* Acyclic form of the `Composition` theorem with strengthening of hypothesis
   (1.) by replacing `util_closure E` with `E` and `util_closure (M_ j)` with
   `M_ j` *)
Theorem Composition0 (E M : prop) (E_ M_ : nat -> prop) :
    (* If... *)
    (* 1. *)
    valid (\A i : ((E \land (\A j : ((LIFT0 (j < i)) \impl (M_ j))))
        \impl (E_ i))) ->
    (* 2. (b) *)
    valid ((E \land (\A j : M_ j))
        \impl M) ->
    (* ...then *)
    valid ((\A j : ((E_ j) \impl (M_ j)))
        \impl (E \impl M)).
Proof.
(* TODO *) Admitted.

(* Ref: "Conjoining Specifications" Theorem 2 (General Decomposition Theorem) *)
(* The hypothesis "v is a tuple of variables including all the free variables of
   Mi" ("Conjoining Specifications", Theorem 2) is omitted. Instead, as
   suggested in SCP, "The theorem does not [need to] make any assumption about
   v". *)
(* The definition adds `(\A j : ((LIFT0 (j < i)) \impl (M_ j)))` to hypothesis
   (2) b as is done in `Decomposition` (SCP, Theorem 8.7) but missing from
   Theorem 2. *)
Theorem GeneralDecomposition {V : Type} (v : State -> V) (E : prop) (E_ Ml_ M_ : nat -> prop) :
    util_stuttering_closed E  ->
    (forall i : nat,
            util_stuttering_closed (Ml_ i))  ->
    (* If... *)
    (* (1) *)
    (forall i : nat,
            valid (((util_closure E) \land (\A j : (util_closure (M_ j))))
                \impl (E_ i))) ->
    (* (2) (a) *)
    (forall i : nat,
            valid (((util_plus_operator (util_closure (E_ i)) v) \land (util_closure (Ml_ i)))
                \impl (util_closure (M_ i)))) ->
    (* (2) (b) *)
    (forall i : nat,
            valid (((E_ i) \land ((Ml_ i) \land (\A j : ((LIFT0 (j < i)) \impl (M_ j)))))
                \impl (M_ i))) ->
    (* ...then *)
    (* (a) *)
    valid (((util_plus_operator (util_closure E) v) \land (\A j : (util_closure (Ml_ j))))
        \impl (\A j : (util_closure (M_ j))))
    (* (b) *)
    /\ valid ((E \land (\A j : Ml_ j))
        \impl (\A j : M_ j)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
(* Acyclic form of the `GeneralDecomposition` theorem with strengthening of
   hypothesis (1) by replacing `util_closure E` with `E` and
   `util_closure (M j)` with `M j` *)
Theorem GeneralDecomposition0 (E : prop) (E_ Ml_ M_ : nat -> prop) :
    (* If... *)
    (* (1) *)
    (forall i : nat,
            valid ((E \land (\A j : ((LIFT0 (j < i)) \impl (M_ j))))
                \impl (E_ i))) ->
    (* (2) (b) *)
    (forall i : nat,
            valid (((E_ i) \land ((Ml_ i) \land (\A j : ((LIFT0 (j < i)) \impl (M_ j)))))
                \impl (M_ i))) ->
    (* ...then *)
    (* (b) *)
    valid ((E \land (\A j : Ml_ j))
        \impl (\A j : M_ j)).
Proof.
(* TODO *) Admitted.

End rules.
