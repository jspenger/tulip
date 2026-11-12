Require Import Classical.
Require Import tulip.tla.TLA.
Require Import tulip.tla.lib.LL94_2.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* Quantification                                                             *)
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
