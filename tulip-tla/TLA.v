Require Import PeanoNat.

(* ========================================================================== *)
(* A TLA embedding in Coq based on Leslie Lamport's many works on the         *)
(* "temporal logic of actions". A good first reference is:                    *)
(* > Leslie Lamport. 1994. The temporal logic of actions. ACM Trans. Program. *)
(* > Lang. Syst. 16, 3 (May 1994), 872-923.                                   *)
(* > https://doi.org/10.1145/177492.177726                                    *)
(* If you find this interesting then also check out the official TLA+         *)
(* repositories:                                                              *)
(* > https://github.com/tlaplus                                               *)
(* This project is not affiliated with the TLA+/tlaplus project.              *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Core definitions                                                           *)
(* ========================================================================== *)

Definition behavior (State : Type) : Type :=
    nat -> State.

Definition property (State : Type) : Type :=
    behavior State -> Prop.

(* |= `F`, i.e., F is true for all behaviors *)
Definition valid {State : Type} (F : property State) : Prop :=
    forall beh : behavior State, F beh.

(* ========================================================================== *)
(* Utility definitions                                                        *)
(* ========================================================================== *)

Definition util_monotone (f : nat -> nat) : Prop :=
    forall n, f n <= f (S n).

Definition util_surjective (f: nat -> nat) : Prop :=
    forall m, exists n, f n = m.

Definition util_stuttering_equivalent {State : Type} (b c : behavior State) : Prop :=
    exists f g : nat -> nat,
        util_monotone f
        /\ util_monotone g
        /\ util_surjective f
        /\ util_surjective g
        /\ (forall n : nat, b (f n) = c (g n)).

(* Stuttering equivalent with respect to relation `R`. *)
Definition util_stuttering_equivalent0 {State1 State2 : Type} (R : State1 -> State2 -> Prop) (b : behavior State1) (c : behavior State2) : Prop :=
    exists f g : nat -> nat,
        util_monotone f
        /\ util_monotone g
        /\ util_surjective f
        /\ util_surjective g
        /\ (forall n : nat, R (b (f n)) (c (g n))).

Definition util_stuttering_closed {State : Type} (P : property State) : Prop :=
    forall b c : behavior State,
        util_stuttering_equivalent b c ->
            P b ->
                P c.

Definition util_stuttering_closure {State : Type} (P : property State) : property State :=
    fun c =>
        exists b : behavior State,
            util_stuttering_equivalent b c
            /\ P b.

Definition util_suffix {State : Type} (beh : behavior State) (k : nat) : behavior State :=
    fun j => beh (k + j).

(* ========================================================================== *)
(* TLA embedding                                                              *)
(* ========================================================================== *)

Section tla.
    Context {State : Type}.
    Local Notation prop := (property State).

    (* Lift Coq expressions. *)

    Definition Lift  (q : behavior State -> Prop) : prop :=
        q.
    Definition Lift0 (p : Prop) : prop :=
        fun _ => p.
    Definition Lift1 (state_predicate : State -> Prop) : prop :=
        fun beh => state_predicate (beh 0).
    Definition Lift2 (action : State -> State -> Prop) : prop :=
        fun beh => action (beh 0) (beh 1).

    (* Temporal expressions (Part I). *)

    (* F' *)
    Definition Prime (F : prop) : prop :=
        fun beh => F (util_suffix beh 1).

    (* []F *)
    Definition Always (F : prop) : prop :=
        fun beh => forall k : nat, F (util_suffix beh k).

    (* <>F *)
    Definition Eventually (F : prop) : prop :=
      fun beh => exists k : nat, F (util_suffix beh k).

    (* ENABLED(F) *)
    (* Lamport's ENABLED is defined on "Actions" whereas this definition is on
       behaviors. *)
    Definition Enabled (F : prop) : prop :=
        fun beh => exists beh' : behavior State, beh' 0 = beh 0 /\ F beh'.

    (* Logic expressions. *)

    (* \lnot F *)
    Definition Not (F : prop) : prop :=
        fun beh => ~ F beh.

    (* F \land G *)
    Definition And (F G : prop) : prop :=
        fun beh => F beh /\ G beh.

    (* F \lor G *)
    Definition Or (F G : prop) : prop :=
        fun beh => F beh \/ G beh.

    (* F \impl G *)
    Definition Implication (F G : prop) : prop :=
        fun beh => F beh -> G beh.

    (* F \equiv G *)
    Definition Iff (F G : prop) : prop :=
        fun beh => F beh <-> G beh.

    (* \E x \in A : F(x) *)
    Definition Exists {A : Type} (F : A -> prop) : prop :=
        fun beh => exists x : A, F x beh.

    (* \A x \in A : F(x) *)
    Definition Forall {A : Type} (F : A -> prop) : prop :=
        fun beh => forall x : A, F x beh.

    (* UNCHANGED e, i.e. e' = e *)
    Definition Unchanged {V : Type} (e : State -> V) : prop :=
        Lift2 (fun s s' => e s = e s').

    (* Syntactic sugar. *)

    (* F \leadsto G *)
    Definition LeadsTo (F G : prop) : prop :=
        Always (Implication F (Eventually G)).

    (* [F]_e *)
    Definition Stutter (F : prop) {V : Type} (e : State -> V) : prop :=
        Or F (Unchanged e).

    (* <<A>>_e *)
    Definition NonStutter (A : prop) {V : Type} (e : State -> V) : prop :=
        And A (Not (Unchanged e)).

    (* IF A THEN F ELSE G *)
    Definition IfThenElse (A F G : prop) : prop :=
        And (Implication A F) (Implication (Not A) G).

    (* Fairness. *)

    (* WF_e(F) *)
    Definition WeakFairness {V : Type} (e : State -> V) (F : prop) : prop :=
        LeadsTo
            (Always (Enabled (NonStutter F e)))
            (NonStutter F e).

    (* SF_e(F) *)
    Definition StrongFairness {V : Type} (e : State -> V) (F : prop) : prop :=
        LeadsTo
            (Always (Eventually (Enabled (NonStutter F e))))
            (NonStutter F e).

End tla.

(* Temporal expressions (Part II). *)

(* `F` WITH `abstraction_function` *)
Definition RefinementMapping {State1 State2 : Type} (abstraction_function : State1 -> State2) (F : property State1) : property State2 :=
    fun beh2 =>
        exists beh1 : behavior State1,
            (util_stuttering_equivalent (fun n : nat => abstraction_function (beh1 n)) beh2)
            /\ (F beh1).

(* `F` CO_WITH `abstraction_function` *)
Definition CoRefinementMapping {State1 State2 : Type} (abstraction_function : State1 -> State2) (F : property State1) : property State2 :=
    fun beh2 =>
        forall beh1 : behavior State1,
            (util_stuttering_equivalent (fun n : nat => abstraction_function (beh1 n)) beh2)
            -> (F beh1).

(* `F` WITH0 `abstraction_relation` *)
(* This is a generalization of the "temporal existential quanitification"
   operator. `\EE x: F` is equivalent to `F WITH0 equal_up_to_x` where
   `equal_up_to_x` is an abstraction relation that contains pairs of states
   that are equal for all variables that are not `x`. *)
Definition RefinementMapping0 {State1 State2 : Type} (abstraction_relation : State1 -> State2 -> Prop) (F : property State1) : property State2 :=
    fun beh2 =>
        exists beh1: behavior State1,
            (util_stuttering_equivalent0 abstraction_relation beh1 beh2)
            /\ F beh1.

(* `F` CO_WITH0 `abstraction_relation` *)
Definition CoRefinementMapping0 {State1 State2 : Type} (abstraction_relation : State1 -> State2 -> Prop) (F : property State1) : property State2 :=
    fun beh2 =>
        forall beh1: behavior State1,
            (util_stuttering_equivalent0 abstraction_relation beh1 beh2)
            -> F beh1.

(* ========================================================================== *)
(* Notation                                                                   *)
(* ========================================================================== *)

Declare Scope tla_scope.
Delimit Scope tla_scope with tla.

(* Use `valid F` instead of `|= F`. "Metaformulas" should by convention use
   their defined names to distinguish them from "TLA formulas". *)
(* Notation "|= F" :=
    (valid F)
    (at level 98, F at level 98) : tla_scope. *)

Notation "F '" :=
    (Prime F)
    (at level 10, left associativity) : tla_scope.

Notation "[] F" :=
    (Always F)
    (at level 20, right associativity) : tla_scope.

Notation "'ENABLED' F" :=
    (Enabled F)
    (at level 20, right associativity) : tla_scope.

Notation "'LIFT' expr" :=
    (Lift expr)
    (at level 20, right associativity) : tla_scope.

Notation "'LIFT0' expr" :=
    (Lift0 expr)
    (at level 20, right associativity) : tla_scope.

Notation "'LIFT1' expr" :=
    (Lift1 expr)
    (at level 20, right associativity) : tla_scope.

Notation "'LIFT2' expr" :=
    (Lift2 expr)
    (at level 20, right associativity) : tla_scope.

Notation "\lnot F" :=
    (Not F)
    (at level 75, right associativity) : tla_scope.

Notation "F \land G" :=
    (And F G)
    (at level 80, right associativity) : tla_scope.

Notation "F \lor G" :=
    (Or F G)
    (at level 85, right associativity) : tla_scope.

Notation "F \impl G" :=
    (Implication F G)
    (at level 90, right associativity) : tla_scope.

Notation "F \equiv G" :=
    (Iff F G)
    (at level 90, no associativity) : tla_scope.

Notation "'\E' x \in T : F" :=
    (Exists (fun x : T => F))
    (at level 100, x ident, T at level 99, F at level 100) : tla_scope.

Notation "'\E' x : F" :=
    (Exists (fun x => F))
    (at level 100, x ident, F at level 100) : tla_scope.

Notation "'\A' x \in T : F" :=
    (Forall (fun x : T => F))
    (at level 100, x ident, T at level 99, F at level 100) : tla_scope.

Notation "'\A' x : F" :=
    (Forall (fun x => F))
    (at level 100, x ident, F at level 100) : tla_scope.

Notation "F 'WITH' r" :=
    (RefinementMapping r F)
    (at level 100, r at level 0) : tla_scope.

Notation "F 'CO_WITH' r" :=
    (CoRefinementMapping r F)
    (at level 100, r at level 0) : tla_scope.

Notation "F 'WITH0' R" :=
    (RefinementMapping0 R F)
    (at level 100, R at level 0) : tla_scope.

Notation "F 'CO_WITH0' R" :=
    (CoRefinementMapping0 R F)
    (at level 100, R at level 0) : tla_scope.

Notation "<> F" :=
    (Eventually F)
    (at level 20, right associativity) : tla_scope.

Notation "F \leadsto G" :=
    (LeadsTo F G)
    (at level 90, right associativity) : tla_scope.

Notation "'UNCHANGED' F" :=
    (Unchanged F)
    (at level 20, right associativity) : tla_scope.

Notation "[ F ]_ vars" :=
    (Stutter F vars)
    (at level 20, F at level 100, vars at level 0) : tla_scope.

Notation "<< F >>_ vars" :=
    (NonStutter F vars)
    (at level 20, F at level 100, vars at level 0) : tla_scope.

Notation "'WF_' vars ( A )" :=
    (WeakFairness vars A)
    (at level 20, vars at level 0, A at level 100) : tla_scope.

Notation "'SF_' vars ( A )" :=
    (StrongFairness vars A)
    (at level 20, vars at level 0, A at level 100) : tla_scope.

Notation "'IF' P 'THEN' F 'ELSE' G" :=
    (IfThenElse P F G)
    (at level 100, P at level 100, F at level 100, G at level 100, right associativity) : tla_scope.

(* Notation "'LET' x ':=' e 'IN' F" :=
    (let x := e in F)
    (at level 100, x ident, e at level 100, F at level 100, right associativity) : tla_scope. *)
