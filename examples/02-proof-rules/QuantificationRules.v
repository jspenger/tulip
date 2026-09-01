Require Import Coq.Strings.String.
Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated):                        *)
(* [1]                                                                      *)
(* > Leslie Lamport. 1994. The temporal logic of actions. ACM Trans. Program. *)
(* > Lang. Syst. 16, 3 (May 1994), 872-923.                                   *)
(* > https://doi.org/10.1145/177492.177726                                    *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Quantification                                                             *)
(* ========================================================================== *)

(* ========================================================================== *)
(* State                                                                      *)
(* ========================================================================== *)

(* The type of `State` is a function type from `string` variable names to a
   parametric value type `V`. We do so as "quantification" rules that quantify
   over "variables" require us to define the state type such that we can
   express the meaning of two states agreeing on every variable except `x` (see 
   `equal_up_to_x` below). In contrast, the other proof-rule files leave
   `State` undefined. *)
Definition State (V : Type) : Type := string -> V.

(* ========================================================================== *)
(* Utility functions                                                          *)
(* ========================================================================== *)

(* The name `equal_up_to_x` is from Abadi and Merz's "On TLA as a Logic". It is
   referred to as `=_x` in [1]. *)
#[local] Definition equal_up_to_x {V : Type} (x : string) (s t : State V) : Prop :=
    forall y, y <> x -> s y = t y.

#[local] Lemma equal_up_to_x_refl {V : Type} (x : string) (s : State V) :
    equal_up_to_x x s s.
Proof. intros y _. reflexivity. Qed.

(* ========================================================================== *)
(* Definitions                                                                *)
(* ========================================================================== *)

(* \EE `x`: `F` *)
Definition EExists {V : Type} (x : string) (F : property (State V)) : property (State V) :=
    RefinementMapping0 (equal_up_to_x x) F.

(* \AA `x`: `F` *)
Definition FForall {V : Type} (x : string) (F : property (State V)) : property (State V) :=
    CoRefinementMapping0 (equal_up_to_x x) F.

Notation "'\EE' x : F" :=
    (EExists x F)
    (at level 100, x at level 0, F at level 100) : tla_scope.

Notation "'\AA' x : F" :=
    (FForall x F)
    (at level 100, x at level 0, F at level 100) : tla_scope.

(* ========================================================================== *)
(* Rules                                                                      *)
(* ========================================================================== *)

(* E1 from [1] *)
Lemma EE1 {V : Type} (x : string) (F : property (State V)) :
    valid (F \impl (\EE x : F)).
Proof.
(* TODO *) Admitted.

(* E2 from [1] *)
Lemma EE2 {V : Type} (x : string) (F G : property (State V)) :
    valid ((\EE x : G) \impl G) -> (* x not free in G *)
        valid (F \impl G) ->
            valid ((\EE x : F) \impl G).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma EE3 {V : Type} (x : string) (F G : property (State V)) :
    valid (F \impl G)
        -> valid ((\EE x : F) \impl (\EE x : G)).
Proof.
(* TODO *) Admitted.

(* E1 from [1] adapted to \AA *)
Lemma FF1 {V : Type} (x : string) (F : property (State V)) :
    valid ((\AA x : F) \impl F).
Proof.
(* TODO *) Admitted.

(* E2 from [1] adapted to \AA *)
Lemma FF2 {V : Type} (x : string) (F G : property (State V)) :
    valid (G \impl (\AA x : G)) -> (* x not free in G *)
        valid (G \impl F) ->
            valid (G \impl (\AA x : F)).
Proof.
(* TODO *) Admitted.

(* Not from refs *)
Lemma FF3 {V : Type} (x : string) (F G : property (State V)) :
    valid (F \impl G)
        -> valid ((\AA x : F) \impl (\AA x : G)).
Proof.
(* TODO *) Admitted.
