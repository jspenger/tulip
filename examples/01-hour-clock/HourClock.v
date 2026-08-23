Require Import PeanoNat.
Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.


(* ========================================================================== *)
(* The hour-clock (HC) specification is adapted from:                         *)
(* > Leslie Lamport. 2002. Specifying Systems: The TLA+ Language and Tools    *)
(* > for Hardware and Software Engineers. Addison-Wesley.                     *)
(* The hour-minute-clock (HCM) specification is adapted from:                 *)
(* > Leslie Lamport, Stephan Merz. 2017. Auxiliary Variables in TLA+. CoRR    *)
(* > abs/1703.05121. https://arxiv.org/abs/1703.05121.                        *)
(* ========================================================================== *)

(* ========================================================================== *)
(* The hour clock                                                             *)
(* ========================================================================== *)

Module HC.
    Record State := { hour : nat }.
    Local Notation prop := (property State).
    Definition vars (s : State) : State := s.

    Definition Init : prop := Lift1 (fun s => 
        1 <= hour s <= 12
    ).

    Definition Next : prop := Lift2 (fun s s' => 
        hour s' = (hour s mod 12) + 1
    ).

    Definition Spec : prop := (
        Init \land [][Next]_vars
    ).
End HC.


(* ========================================================================== *)
(* Safety                                                                     *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Safety: valid (HC.Spec \impl Type_OK), valid (HC.Spec \impl Incr_OK)       *)
(* ========================================================================== *)

Definition Type_OK : property HC.State := [] Lift1 (fun s =>
    1 <= HC.hour s <= 12
).

Definition Incr_OK : property HC.State := [] Lift2 (fun s s' =>
    match HC.hour s with
        | 1  => HC.hour s' = 1  \/ HC.hour s' = 2
        | 2  => HC.hour s' = 2  \/ HC.hour s' = 3
        | 3  => HC.hour s' = 3  \/ HC.hour s' = 4
        | 4  => HC.hour s' = 4  \/ HC.hour s' = 5
        | 5  => HC.hour s' = 5  \/ HC.hour s' = 6
        | 6  => HC.hour s' = 6  \/ HC.hour s' = 7
        | 7  => HC.hour s' = 7  \/ HC.hour s' = 8
        | 8  => HC.hour s' = 8  \/ HC.hour s' = 9
        | 9  => HC.hour s' = 9  \/ HC.hour s' = 10
        | 10 => HC.hour s' = 10 \/ HC.hour s' = 11
        | 11 => HC.hour s' = 11 \/ HC.hour s' = 12
        | 12 => HC.hour s' = 12 \/ HC.hour s' = 1
        | _ => True
    end
).

Theorem hc_impl_type_ok :
    valid (
        HC.Spec \impl Type_OK
    ).
Proof.
    (* The proof is left as an exercise for the reader ;-) *)
    admit.
Admitted.

Theorem hc_impl_incr_ok :
    valid (
        HC.Spec \impl Incr_OK
    ).
Proof.
    admit.
Admitted.


(* ========================================================================== *)
(* Safety props imply hc: valid ((Type_OK \land Incr_OK) \impl HC.Spec)       *)
(* ========================================================================== *)

Theorem safety_impl_hc :
    valid (
        (Type_OK \land Incr_OK) \impl HC.Spec
    ).
Proof.
    admit.
Admitted.


(* ========================================================================== *)
(* Liveness                                                                   *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Liveness: The hour clock visits every hour (1..12) infinitely often        *)
(* ========================================================================== *)

Definition HC_Is_Live : property HC.State :=
    \A x \in { x : nat | 1 <= x <= 12 } : (
        []<> Lift1 (fun s =>
            HC.hour s = proj1_sig x
        )
    ).


(* ========================================================================== *)
(* Hour clock is not live: ~ valid (HC.Spec \impl HC_Is_Live)                 *)
(* ========================================================================== *)

Theorem not_hc_impl_live :
    ~ valid (
        HC.Spec \impl HC_Is_Live
    ).
Proof.
    admit.
Admitted.


(* ========================================================================== *)
(* Fair hour clock is live: valid ((HC.Spec \land F) \impl HC_Is_Live)        *)
(* ========================================================================== *)

Definition F : property HC.State :=
    WF_(HC.vars) (HC.Next).

Theorem fair_hc_impl_live :
    valid (
        (HC.Spec \land F) \impl HC_Is_Live
    ).
Proof.
    admit.
Admitted.


(* ========================================================================== *)
(* Refinemenet                                                                *)
(* ========================================================================== *)

(* ========================================================================== *)
(* The hour-minute clock                                                      *)
(* ========================================================================== *)

Module HMC.
    Record State := { hour : nat ; minute : nat }.
    Local Notation prop := (property State).
    Definition vars (s : State) : State := s.

    Definition Init : prop := Lift1 (fun s =>
        1 <= hour s <= 12
            /\ minute s <= 59
    ).

    Definition Next : prop := Lift2 (fun s s' =>
        if minute s <? 59 then
            minute s' = minute s + 1
                /\ hour s' = hour s
        else
            minute s' = 0
                /\ hour s' = (hour s mod 12) + 1
    ).

    Definition Spec : prop := (
        Init \land [][Next]_vars
    ).

    Definition F : property HMC.State :=
        WF_(HMC.vars) (HMC.Next).
End HMC.


(* ========================================================================== *)
(* Refinement: valid ((HMC.Spec WITH r) \impl HC.Spec)                        *)
(* ========================================================================== *)

Definition r (s : HMC.State) : HC.State := 
    HC.Build_State (HMC.hour s).

Theorem hmc_refines_hc : 
    valid (
        (HMC.Spec WITH r) \impl HC.Spec
    ).
Proof.
    admit.
Admitted.

Theorem hc_refines_hmc : 
    valid (
        HC.Spec \impl (HMC.Spec WITH r)
    ).
Proof.
    admit.
Admitted.

Theorem hmc_equiv_hc : 
    valid (
        (HMC.Spec WITH r) \equiv HC.Spec
    ).
Proof.
    admit.
Admitted.


(* ========================================================================== *)
(* Refinement with fairness                                                   *)
(* ========================================================================== *)

Theorem fair_hmc_refines_fair_hc : 
    valid (
        ((HMC.Spec \land HMC.F) WITH r) \impl (HC.Spec \land F)
    ).
Proof.
    admit.
Admitted.

Theorem fair_hc_refines_fair_hmc : 
    valid (
        (HC.Spec \land F) \impl ((HMC.Spec \land HMC.F) WITH r)
    ).
Proof.
    admit.
Admitted.

Theorem fair_hmc_equiv_fair_hc : 
    valid (
        ((HMC.Spec \land HMC.F) WITH r) \equiv (HC.Spec \land F)
    ).
Proof.
    admit.
Admitted.
