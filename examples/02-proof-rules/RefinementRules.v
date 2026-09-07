Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

Section rules.

Context {State1 State2 : Type}.

(* TODO: Keep only the useful rules... *)

(* ========================================================================== *)
(* Utility definitions                                                        *)
(* ========================================================================== *)

(* Not from refs *)
Definition util_inverse (r : State1 -> State2) (s2 : State2) (s1 : State1) : Prop :=
    r s1 = s2.

(* Not from refs *)
Definition util_inverse0 (r : State1 -> State2 -> Prop) (s2 : State2) (s1 : State1) : Prop :=
    r s1 s2.

(* Not from refs *)
Definition util_reflexive (f : State1 -> State1) : Prop :=
    forall s1, f s1 = s1.

(* Not from refs *)
Definition util_reflexive0 (r: State1 -> State1 -> Prop) : Prop :=
    forall s1, r s1 s1.

(* Not from refs *)
Definition util_symmetric (f : State1 -> State1) : Prop :=
    forall s1, f (f s1) = s1.

(* Not from refs *)
Definition util_symmetric0 (r : State1 -> State1 -> Prop) : Prop :=
    forall s1 s2, r s1 s2 -> r s2 s1.

(* Not from refs *)
Definition util_partial_function0 (r : State1 -> State2 -> Prop) : Prop :=
    forall s1 s2 s3, r s1 s2 -> r s1 s3 -> s2 = s3.

(* Not from refs *)
(* The refinement mapping operator `RefinementMapping` but __not__ stuttering
   closed *)
Definition util_with2 {S1 S2 : Type} (f : S1 -> S2) (F : property S1) : property S2 :=
    fun beh2 =>
        exists beh1 : behavior S1,
            (forall n : nat, f (beh1 n) = beh2 n)
            /\ F beh1.

(* Not from refs *)
(* The refinement mapping operator `CoRefinementMapping` but __not__ stuttering
   closed *)
Definition util_co_with2 {S1 S2 : Type} (f : S1 -> S2) (F : property S1) : property S2 :=
    fun beh2 =>
        forall beh1 : behavior S1,
            (forall n : nat, f (beh1 n) = beh2 n)
            -> F beh1.

(* Not from refs *)
(* The refinement mapping operator `RefinementMapping0` but __not__ stuttering
   closed *)
Definition util_with02 {S1 S2 : Type} (r : S1 -> S2 -> Prop) (F : property S1) : property S2 :=
    fun beh2 =>
        exists beh1 : behavior S1,
            (forall n : nat, r (beh1 n) (beh2 n))
            /\ F beh1.

(* Not from refs *)
(* The refinement mapping operator `CoRefinementMapping0` but __not__ stuttering
   closed *)
Definition util_co_with02 {S1 S2 : Type} (r : S1 -> S2 -> Prop) (F : property S1) : property S2 :=
    fun beh2 =>
        forall beh1 : behavior S1,
            (forall n : nat, r (beh1 n) (beh2 n))
            -> F beh1.

(* ========================================================================== *)
(* Utility lemmas                                                             *)
(* ========================================================================== *)

(* Not from refs *)
Lemma AUX1 (Op : property State1 -> property State2) (F G : property State1) :
    (forall F G : property State1, valid (F \impl G) -> valid ((Op F) \impl (Op G))) ->
        valid (Op (F \land G)
            \impl (Op F) \land (Op G)).
Proof.
(* TODO *) Admitted. 

(* Not from refs *)
Lemma AUX2 (Op : property State1 -> property State2) (F_ : nat -> property State1) :
    (forall F G : property State1, valid (F \impl G) -> valid ((Op F) \impl (Op G))) ->
        valid (Op (\A i : F_ i)
            \impl \A i : Op (F_ i)).
Proof.
(* TODO *) Admitted.

(* ========================================================================== *)
(* Refinement Mapping / 0                                                     *)
(* ========================================================================== *)

(* Note: not from references *)
(* Refinement version of EE1 *)
Lemma RM1 (f : State1 -> State1) (F : property State1) :
    util_reflexive f ->
        valid (F \impl (F WITH f)).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE1 *)
Lemma R0M1 (r : State1 -> State1 -> Prop) (F : property State1) :
    util_reflexive0 r ->
        valid (F \impl (F WITH0 r)).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE2 *)
Lemma RM2 (f: State1 -> State1) (F G : property State1) :
    valid (G WITH f \impl G) (* cf. "x not free in G" with "x" as f in EE2 *)
        -> valid (F \impl G)
            -> valid (F WITH f \impl G).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE2 *)
Lemma R0M2 (r: State1 -> State1 -> Prop) (F G : property State1) :
    valid (G WITH0 r \impl G) (* cf. "x not free in G" with "x" as f in EE2 *)
        -> valid (F \impl G)
            -> valid (F WITH0 r \impl G).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE3 *)
Lemma RM3 (f : State1 -> State2) (F G : property State1) :
    valid (F \impl G)
        -> valid ((F WITH f) \impl (G WITH f)).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
(* Refinement version of EE3 *)
Lemma R0M3 (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid (F \impl G)
        -> valid ((F WITH0 r) \impl (G WITH0 r)).
Proof.
(* TODO *) Admitted.

(* Note: not from references *)
Lemma RM4 (f : State1 -> State2) (F G : property State1) :
    util_injective f ->
        util_stuttering_closed G ->
            valid ((F WITH f) \impl (G WITH f)) ->
                valid (F \impl G).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM5a (f : State1 -> State2) (F G : property State1) :
    valid (((F \land G) WITH f)
        \impl ((F WITH f) \land (G WITH f))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM5b (f : State1 -> State2) (F_ : nat -> property State1) :
    valid (((\A i : F_ i) WITH f)
        \impl (\A i : (F_ i WITH f))).
Proof.
(* TODO *) Admitted.

Lemma RM5c (f : State1 -> State2) (F G : property State1) :
    valid (((F WITH f) \land (G CO_WITH f))
        \impl ((F \land G) WITH f)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M5a (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid (((F \land G) WITH0 r)
        \impl ((F WITH0 r) \land (G WITH0 r))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M5b (r : State1 -> State2 -> Prop) (F_ : nat -> property State1) :
    valid (((\A i : F_ i) WITH0 r)
        \impl (\A i : (F_ i WITH0 r))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M5c (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid (((F WITH0 r) \land (G CO_WITH0 r))
        \impl ((F \land G) WITH0 r)).
Proof.
(* TODO *) Admitted.

(* Frobenius reciprocity `->` direction *)
(* Not from refs *)
Lemma RM6a (r : State1 -> State2) (F : property State2) (G : property State1) :
    util_stuttering_closed F ->
        valid ((((F WITH0 (util_inverse r)) \land G) WITH r)
            \impl (F \land (G WITH r))).
Proof.
(* TODO *) Admitted.

(* Frobenius reciprocity `->` direction *)
(* Not from refs *)
Lemma R0M6a (f : State1 -> State2 -> Prop) (F : property State2) (G : property State1) :
    util_partial_function0 f ->
        util_stuttering_closed F ->
            valid ((((F WITH0 (util_inverse0 f)) \land G) WITH0 f)
                \impl (F \land (G WITH0 f))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
(* Frobenius reciprocity `<-` direction *)
Lemma RM6b (r : State1 -> State2) (F : property State2) (G : property State1) :
    valid ((F \land (G WITH r))
        \impl (((F WITH0 (util_inverse r)) \land G) WITH r)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
(* Frobenius reciprocity `<-` direction *)
Lemma R0M6b (f : State1 -> State2 -> Prop) (F : property State2) (G : property State1) :
    valid ((F \land (G WITH0 f))
        \impl (((F WITH0 (util_inverse0 f)) \land G) WITH0 f)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM7 (f : State1 -> State2) (F : property State1) (G : property State2) :
    valid (F WITH f \impl G) <->
        valid (F \impl (G CO_WITH0 (util_inverse f))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M7 (f : State1 -> State2 -> Prop) (F : property State1) (G : property State2) :
    valid (F WITH0 f \impl G) <->
        valid (F \impl (G CO_WITH0 (util_inverse0 f))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM8 (f : State1 -> State2) (F : property State2) (G : property State1) :
    valid (F WITH0 (util_inverse f) \impl G) <->
        valid (F \impl (G CO_WITH f)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M8 (f : State1 -> State2 -> Prop) (F : property State2) (G : property State1) :
    valid (F WITH0 (util_inverse0 f) \impl G) <->
        valid (F \impl (G CO_WITH0 f)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM9 (f : State1 -> State1) (G : property State1) :
    util_symmetric f ->
        valid ((G WITH f) \impl G) ->
            valid (G \impl (G CO_WITH f)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma R0M9 (r : State1 -> State1 -> Prop) (G : property State1) :
    util_symmetric0 r ->
        valid ((G WITH0 r) \impl G) ->
            valid (G \impl (G CO_WITH0 r)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM10a (f : State1 -> State2) (F : property State1) :
    valid ((util_with2 f F) \impl (F WITH f)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM10b (f : State1 -> State2) (F : property State1) :
    valid ((F CO_WITH f) \impl (util_co_with2 f F)).
Proof.
(* TODO *) Admitted.

Lemma RM11a (f : State1 -> State2) (F : property State2) :
    util_stuttering_closed F ->
        valid ((F WITH0 (util_inverse f))
            \impl (util_with02 (util_inverse f) F)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM11b (f : State1 -> State2) (F : property State2) :
    util_stuttering_closed F ->
        valid ((util_co_with02 (util_inverse f) F)
            \impl (F CO_WITH0 (util_inverse f))).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma RM12 (f : State1 -> State2) (Bl : property State1) (A B : property State2) :
    util_stuttering_closed A ->
        util_stuttering_closed B ->
            valid (((util_with02 (util_inverse f) A) \land Bl)
                \impl (util_co_with02 (util_inverse f) B)) ->
                    valid ((A \land (Bl WITH f)) \impl B).
Proof.
(* TODO *) Admitted.

End rules.
