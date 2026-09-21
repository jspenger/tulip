Require Import tulip.tla.TLA.

#[local] Open Scope tla_scope.

Section rules.

Context {State : Type}.
#[local] Notation prop := (property State).

(* TODO: add references *)

(* ========================================================================== *)
(* Well formed                                                                *)
(* -------------------------------------------------------------------------- *)
(* A formula is `WellFormed` if it is constructed from the definitions of     *)
(* TLA.v and adheres to the restrictions of the `WellFormed` inductive.       *)
(* A well-formed formula is stuttering closed                                 *)
(* ([wellformed_stuttering_closed]).                                          *)
(* ========================================================================== *)

(* Well-formed formula indexed by four levels:
   - Level 0: logic propositions (e.g., lifted Coq propositions)
   - Level 1: state predicates
   - Level 2: actions
   - Level 3: temporal formulas *)
Inductive WellFormedN : nat -> prop -> Prop :=
    (* meta *)

    (* weakening l0 -> l1-3 and l1 -> l2-3 *)
    | wf_weaken
            (l l' : nat)
            (F : prop) :
        l <= 1 -> l <= l' -> l' <= 3 -> WellFormedN l F -> WellFormedN l' F

    (* prime appl weakening l1 -> l2 *)
    | wf_prime
            (l : nat)
            (F : prop) :
        l <= 1 -> WellFormedN l F -> WellFormedN 2 (F ')

    (* lift *)

    (* logic proposition l0 *)
    | wf_lift0
            (p : Prop) :
        WellFormedN 0 (\lift0 p)

    (* state predicate l1 *)
    | wf_lift1
            (p : State -> Prop) :
        WellFormedN 1 (\lift1 p)

    (* action l2 *)
    | wf_lift2
            (a : State -> State -> Prop) :
        WellFormedN 2 (\lift2 a)

    (* temporal (part i) *)

    | wf_always
            (F : prop) :
        WellFormedN 3 F -> WellFormedN 3 ([]F)

    | wf_eventually
            (F : prop) :
        WellFormedN 3 F -> WellFormedN 3 (<>F)

    (* enabled appl ? -> l1 *)
    | wf_enabled
            (l : nat)
            (F : prop) :
        WellFormedN l F -> WellFormedN 1 (\enabled F)

    (* logic *)

    | wf_lnot
            (l : nat)
            (F : prop) :
        WellFormedN l F -> WellFormedN l (\lnot F)

    | wf_land
            (l : nat)
            (F G : prop) :
        WellFormedN l F -> WellFormedN l G -> WellFormedN l (F \land G)

    | wf_lor
            (l : nat)
            (F G : prop) :
        WellFormedN l F -> WellFormedN l G -> WellFormedN l (F \lor G)

    | wf_impl
            (l : nat)
            (F G : prop) :
        WellFormedN l F -> WellFormedN l G -> WellFormedN l (F \impl G)

    | wf_equiv
            (l : nat)
            (F G : prop) :
        WellFormedN l F -> WellFormedN l G -> WellFormedN l (F \equiv G)

    | wf_exists
            (l : nat)
            {T : Type}
            (F : T -> prop) :
        (forall x : T, WellFormedN l (F x)) -> WellFormedN l (\E x \st (F x))

    | wf_forall
            (l : nat)
            {T : Type}
            (F : T -> prop) :
        (forall x : T, WellFormedN l (F x)) -> WellFormedN l (\A x \st (F x))

    (* unchanged appl l2 *)
    | wf_unchanged
            {V : Type}
            (e : State -> V) :
        WellFormedN 2 (\unchanged e)

    (* syntactic sugar *)

    | wf_leadsto
            (F G : prop) :
        WellFormedN 3 F -> WellFormedN 3 G -> WellFormedN 3 (F \leadsto G)

    | wf_stutter
            {V : Type}
            (F : prop)
            (e : State -> V) :
        WellFormedN 2 F -> WellFormedN 2 ([F]_e)

    (* [][F]_e appl weakening l2 -> l3 *)
    | wf_always_stutter
            {V : Type}
            (F : prop)
            (e : State -> V) :
        WellFormedN 2 F -> WellFormedN 3 ([][F]_e)

    | wf_nonstutter
            {V : Type}
            (F : prop)
            (e : State -> V) :
        WellFormedN 2 F -> WellFormedN 2 (<<F>>_e)

    (* <><<F>>_e appl weakening l2 -> l3 *)
    | wf_eventually_nonstutter
            {V : Type}
            (F : prop)
            (e : State -> V) :
        WellFormedN 2 F -> WellFormedN 3 (<><<F>>_e)

    | wf_ifthenelse
            (P F G : prop) :
        WellFormedN 3 P -> WellFormedN 3 F -> WellFormedN 3 G -> WellFormedN 3 (\if P \then F \else G)

    (* fairness *)

    | wf_weak_fairness
            {V : Type}
            (e : State -> V)
            (F : prop) :
        WellFormedN 2 F -> WellFormedN 3 (\wf F \sub e)

    | wf_strong_fairness
            {V : Type}
            (e : State -> V)
            (F : prop) :
        WellFormedN 2 F -> WellFormedN 3 (\sf F \sub e)

    (* tempora (part ii) *)

    | wf_refinement_mapping
            {State1 : Type}
            (r : State1 -> State)
            (F : property State1) :
        WellFormedN 3 (F \with r)

    | wf_corefinement_mapping
            {State1 : Type}
            (r : State1 -> State)
            (F : property State1) :
        WellFormedN 3 (F \cowith r)

    | wf_refinement_mapping0
            {State1 : Type}
            (r : State1 -> State -> Prop)
            (F : property State1) :
        WellFormedN 3 (F \with0 r)

    | wf_corefinement_mapping0
            {State1 : Type}
            (r : State1 -> State -> Prop)
            (F : property State1) :
        WellFormedN 3 (F \cowith0 r).

Definition WellFormed0 : prop -> Prop :=
    WellFormedN 0.

Definition WellFormed1 : prop -> Prop :=
    WellFormedN 1.

Definition WellFormed2 : prop -> Prop :=
    WellFormedN 2.

Definition WellFormed3 : prop -> Prop :=
    WellFormedN 3.

(* Well-formed TLA formula. Stuttering closed by
   [wellformed_stuttering_closed]. Alias of [WellFormed3] and
   [WellFormedN 3]. [Kanonical] is well-formed by [kanonical_wellformed]. *)
Definition WellFormed : prop -> Prop :=
    WellFormed3.

(* ========================================================================== *)
(* Kanonical form                                                             *)
(* ========================================================================== *)

(* TODO: change from "Kanonical" to another name. "Canonical" is a Coq
   keyword. *)

(* TLA formula in canonical form as a finite conjunction of `I`, `[][N]_v`, and
   `F`, where `I` is an "initial-state predicate", `N` is a 
   "next-state action", and `F` is a "fairness property" (either WF or SF).
   This encompasses the text-book canonical form `I /\ [][N]_v /\ F`. Kanonical
   form is [WellFormed]. *)
Inductive Kanonical : prop -> Prop :=
    | kacl_i
            (I : prop) :
        WellFormed1 I -> Kanonical I
    | kacl_n
            {V : Type}
            (N : prop)
            (e : State -> V) :
        WellFormed2 N -> Kanonical ([][N]_e)
    | kacl_wf
            {V : Type}
            (F : prop)
            (e : State -> V) :
            (* TODO: change the order of arguments for `WeakFairness` and `StrongFairness` from `e F` to `F e` *)
        WellFormed2 F -> Kanonical (\wf F \sub e)
    | kacl_sf
            {V : Type}
            (F : prop)
            (e : State -> V) :
        WellFormed2 F -> Kanonical (\sf F \sub e)
    | kacl_and
            (F G : prop) :
        Kanonical F -> Kanonical G -> Kanonical (F \land G).

(* ========================================================================== *)
(* Well-formed formula is  stuttering closed                                  *)
(* ========================================================================== *)

Theorem wellformed_stuttering_closed (F : prop) :
    WellFormed F ->
        util_stuttering_closed F.
Proof.
(* TODO *) Admitted.

(* ========================================================================== *)
(* Kanonical form is well formed                                              *)
(* ========================================================================== *)

Theorem kanonical_wellformed (F : prop) :
    Kanonical F ->
        WellFormed F.
Proof.
(* TODO *) Admitted.

Corollary kanonical_stuttering_closed (F : prop) :
    Kanonical F ->
        util_stuttering_closed F.
Proof.
(* TODO *) Admitted.

End rules.
