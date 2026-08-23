Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

Section rules.

Context {State1 State2 : Type}.

(* TODO: Keep only the useful rules... *)

(* ========================================================================== *)
(* Refinement Mapping                                                         *)
(* ========================================================================== *)

(* Note: not from references *)
Lemma RM1 (f : State1 -> State2) (F G : property State1) :
    valid (F \impl G)
        -> valid ((F WITH f) \impl (G WITH f)).
Proof.
    admit.
Admitted.

(* Note: not from references *)
Corollary RM1COR1 (f: State1 -> State1) (F G : property State1) :
    valid (G WITH f \impl G)
        -> valid (F \impl G)
            -> valid (F WITH f \impl G).
Proof.
    admit.
Admitted.

#[local] Definition injective {A B : Type} (f : A -> B) : Prop :=
    forall x y : A,
        f x = f y -> x = y.

(* Note: not from references *)
Lemma RM2 (f : State1 -> State2) (F G : property State1) :
    injective f ->
        util_stuttering_closed G ->
            valid ((F WITH f) \impl (G WITH f)) ->
                valid (F \impl G).
Proof.
    admit.
Admitted.

(* ========================================================================== *)
(* Refinement Mapping 0                                                       *)
(* ========================================================================== *)

(* Note: not from references *)
Lemma R0M1 (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid (F \impl G)
        -> valid ((F WITH0 r) \impl (G WITH0 r)).
Proof.
    admit.
Admitted.

(* Note: not from references *)
Corollary R0M1COR1 (r: State1 -> State1 -> Prop) (F G : property State1) :
    valid (G WITH0 r \impl G)
        -> valid (F \impl G)
            -> valid (F WITH0 r \impl G).
Proof.
    admit.
Admitted.

End rules.
