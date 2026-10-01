Require Import tulip.tla.TLA.
Require Import tulip.tla.x_Base.

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
    reflexivity.
Qed.

(* Note: not from references *)
#[local] Lemma util_beh_eq (b c : behavior State) :
    (forall n : nat, b n = c n) ->
        util_stuttering_equivalent b c.
Proof.
    exact (stuttering_equivalent_pointwise b c).
Qed.

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated):                        *)
(* > Leslie Lamport. 1994. The temporal logic of actions. ACM Trans. Program. *)
(* > Lang. Syst. 16, 3 (May 1994), 872-923.                                   *)
(* > https://doi.org/10.1145/177492.177726                                    *)
(*                                                                            *)
(* Other references:                                                          *)
(* > Stephan Merz. 2003. On the Logic of TLA+. Computing and Informatics. 22, *)
(* > 3-4 (2003), 351-379.                                                     *)
(* ========================================================================== *)

(* ========================================================================== *)
(* The Rules of Simple Temporal Logic                                         *)
(* ========================================================================== *)

Lemma STL1 (F : prop) :
    valid F ->
        valid ([]F).
Proof.
    intros HF beh k. exact (HF (util_suffix beh k)).
Qed.

Lemma STL2 (F : prop) :
    valid ([]F \impl F).
Proof.
    intros beh HF. exact (HF 0).
Qed.

Lemma STL3 (F : prop) :
    util_stuttering_closed F ->
        valid ([][]F \equiv []F).
Proof.
    intros _ beh. split.
    - intros HF k. exact (HF k 0).
    - intros HF k m. rewrite util_suffix_shift. exact (HF (k + m)).
Qed.

Lemma STL4 (F G : prop) :
    valid (F \impl G) ->
        valid ([]F \impl []G).
Proof.
    intros HFG beh HF k. exact (HFG (util_suffix beh k) (HF k)).
Qed.

(* STL4 (Merz, 2003) *)
Lemma STL4_2 (F G : prop) :
    valid (
        [](F \impl G) \impl
            ([]F \impl []G)).
Proof.
    intros beh HFG HF k. exact (HFG k (HF k)).
Qed.

Lemma STL5 (F G : prop) :
    valid (
        [](F \land G) \equiv
            []F \land []G
    ).
Proof.
    intros beh. split.
    - intros HFG. split.
        + intros k. exact (proj1 (HFG k)).
        + intros k. exact (proj2 (HFG k)).
    - intros [HF HG] k. exact (conj (HF k) (HG k)).
Qed.

Lemma STL6 (F G : prop) :
    (util_stuttering_closed F /\ util_stuttering_closed G) ->
        valid (
            <>[]F \land <>[]G
            \equiv
            <>[](F \land G)
        ).
Proof.
    intros _ beh. split.
    - intros [[n Hn] [m Hm]]. exists (Nat.max n m). intros k.
        rewrite util_suffix_shift. split.
        + apply (always_suffix_le F beh n Hn). lia.
        + apply (always_suffix_le G beh m Hm). lia.
    - intros [n Hn]. split.
        + exists n. intros k. exact (proj1 (Hn k)).
        + exists n. intros k. exact (proj2 (Hn k)).
Qed.

Lemma LATTICE (T : Type) (wf_rel : T -> T -> Prop) (F : prop) (H : T -> prop) (G : prop) :
    (util_stuttering_closed G
    /\ (forall c : T, util_stuttering_closed (H c))
    (* The well-founded partial order `wf_rel` is of direction 'less-than'
       whereas Lamport's partial order `\succ` is of direction 'greater-than' *)
    /\ well_founded wf_rel
    /\ valid (
        F \impl (
            \A c \in T \st
                H c \leadsto
                    (G \lor (\E d \in T \st ((Lift0 (wf_rel d c)) \land (H d))))
        )
    ))
    ->
    valid (F \impl ((\E c \st (H c)) \leadsto G)).
Proof.
    intros [_ [_ [Hwf Hprem]]] beh HF k [c Hc]. revert k Hc.
    induction c as [c IHc] using (well_founded_induction Hwf). intros k Hc.
    destruct (Hprem beh HF c k Hc) as [j [HG | [d [Hlt Hd]]]].
    - exists j. exact HG.
    - rewrite util_suffix_shift in Hd.
        destruct (IHc d Hlt (k + j) Hd) as [i HG].
        rewrite util_suffix_shift in HG. exists (j + i).
        rewrite util_suffix_shift, Nat.add_assoc. exact HG.
Qed.

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
    intros HFG HF beh. exact (HFG beh (STL1 F HF beh)).
Qed.

(* Note: not from references *)
#[local] Lemma R2 (F G : prop) :
    valid (F \impl G)
        -> valid F
            -> valid G.
Proof.
    intros HFG HF beh. exact (HFG beh (HF beh)).
Qed.

(* ========================================================================== *)
(* The Basic Rules of TLA                                                     *)
(* ========================================================================== *)

Lemma TLA1 {V : Type} (P : prop) (f : State -> V) :
    util_stuttering_closed P
    ->
    valid (
        (P \land (\unchanged f))
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
    intros _ Hstep beh. split.
    - intros HP. split.
        + exact (HP 0).
        + intros k. left. intros _. rewrite prime_suffix. exact (HP (S k)).
    - intros [HP0 Hbox] k. induction k as [| k IH].
        + exact HP0.
        + rewrite <- prime_suffix. destruct (Hbox k) as [Himp | Hunch].
            * exact (Himp IH).
            * exact (Hstep (util_suffix beh k) (conj IH Hunch)).
Qed.

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
    intros Hsim beh [HP HA]. split.
    - intros k. exact (proj1 (Hsim (util_suffix beh k) (conj (HP k) (HA k)))).
    - intros k. exact (proj2 (Hsim (util_suffix beh k) (conj (HP k) (HA k)))).
Qed.

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
    intros _ Hstep beh [HI HN] k. induction k as [| k IH].
    - exact HI.
    - rewrite <- prime_suffix.
        exact (Hstep (util_suffix beh k) (conj IH (HN k))).
Qed.

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
    intros _ beh HI. split.
    - intros HN k. destruct (HN k) as [HNk | Hunch].
        + left. refine (conj HNk (conj (HI k) _)).
            rewrite prime_suffix. exact (HI (S k)).
        + right. exact Hunch.
    - intros HN k. destruct (HN k) as [[HNk _] | Hunch].
        + left. exact HNk.
        + right. exact Hunch.
Qed.

(* ========================================================================== *)
(* Quantification                                                             *)
(* ========================================================================== *)

Lemma F1 {T : Type} (F : T -> prop) (e : T) :
    valid (
        (F e)
        \impl
        (\E c \st (F c))
    ).
Proof.
    intros beh HF. exists e. exact HF.
Qed.

Lemma F2 {T : Type} (F : T -> prop) (G : prop) :
    valid (
        (\A c \st ((F c) \impl G))
    )
    ->
    valid(
        ((\E c \st (F c)) \impl G)
    ).
Proof.
    intros HFG beh [c HF]. exact (HFG beh c HF).
Qed.

(* E1 (Lamport 1994): See EE1 in examples/02-proof-rules/QuantificationRules.v *)
(* E2 (Lamport 1994): See EE2 in examples/02-proof-rules/QuantificationRules.v *)

End rules.
