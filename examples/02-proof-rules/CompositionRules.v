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
    valid ((\A i : Ml i) \impl (\A i : M i)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
(* Acyclic form of the `Decomposition` theorem with strenghtening of hypothesis 
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

End rules.
