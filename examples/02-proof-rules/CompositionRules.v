Require Import tulip.tla.TLA.
Require Import tulip.tla.x_Stutter.

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
(* Utility definitions                                                        *)
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

(* Not from refs *)
(* Note: the case k=0 corresponds to satisfiability of `P`, i.e., if some
   behavior exists that satisfies `P`. In contrast, `util_tts` considers
   the case k=0 as True. *)
Definition util_extends_from_state {State : Type} (P : property State) (beh : behavior State) (k : nat) : Prop :=
    exists beh' : behavior State,
        P beh'
        /\ (forall n : nat, n < k -> beh' n = beh n).

(* Ref: "Conjoining Specifications", section 3.4 *)
(* The closure of F `C(F)` is defined "such that a behavior \sigma satisfies
   C(F) iff every prefix of \sigma satisfies F". *)
(* `\C(F)` *)
Definition util_closure {State : Type} (F : property State) : property State :=
    fun beh => forall n : nat, util_tts F beh n.

(* Not from refs *)
(* Extraction of the safety property of a property. Alias of `util_closure`. *)
Definition util_prop_safety_of {State : Type} (F : property State) : property State :=
    util_closure F.

(* Not from refs *)
(* Extraction of the liveness property of a property. Alias of `util_closure F
   \impl F`. *)
Definition util_prop_liveness_of {State : Type} (F : property State) : property State :=
    util_closure F \impl F.

(* Ref: "Conjoining Specifications", section 3.4 *)
(* "(P, L) is called machine closed iff C(P /\ L) equals P" *)
(* Note: This definition is only satisfied when F is a safety property. One may
   instead define machine closed as `util_closure(F \land L) \equiv
   util_closure(F)` to express that L does not introduce any new safety
   properties beyond what is implied by F. *)
Definition util_machine_closed {State : Type} (F L : property State) : Prop :=
    valid (util_closure(F \land L) \equiv F).

Definition util_prop_is_safety {State : Type} (F : property State) : Prop :=
    valid (util_closure F \impl F).

Definition util_prop_is_liveness {State : Type} (F : property State) : Prop :=
    valid (util_closure F).

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
(* Utility lemmas                                                             *)
(* ========================================================================== *)

Lemma property_implies_closure {State : Type} (F : property State) :
    valid (F \impl util_closure F).
Proof.
    intros beh HF n. right. exists beh.
    split; [exact HF | intros i _; reflexivity].
Qed.

#[local] Lemma util_tts_agree {State : Type} (P : property State)
        (beh c : behavior State) (n : nat) :
    (forall i : nat, i < n -> beh i = c i) ->
        util_tts P beh n -> util_tts P c n.
Proof.
    intros Hbc [Hn | [d [HP Hag]]]; [left; exact Hn |].
    right. exists d. split; [exact HP |].
    intros i Hi. rewrite (Hag i Hi). exact (Hbc i Hi).
Qed.

#[local] Lemma util_tts_mono {State : Type} (P Q : property State)
        (beh : behavior State) (n : nat) :
    (forall c : behavior State, P c -> util_closure Q c) ->
        util_tts P beh n -> util_tts Q beh n.
Proof.
    intros HPQ [Hn | [c [HP Hag]]]; [left; exact Hn |].
    exact (util_tts_agree Q c beh n Hag (HPQ c HP n)).
Qed.

Lemma machine_closed_def_iff {State : Type} (F L : property State) :
    util_machine_closed F L <->
        (* Ref: SCP Section 4.2.2 *)
        (* "In general, a pair <S, L>, where S is a safety property and L a
           liveness property, is defined to be machine closed iff every finite
           behavior satisfying S can be completed to a behavior satisfying
           S /\ L." *)
        util_prop_is_safety F
        /\ (forall (beh : behavior State) (n: nat),
                (* The definition of `util_tts` states that some behavior
                   with prefix `beh` up to state `n` satisfies `F` *)
                (util_tts F beh n) ->
                    (util_tts (F \land L) beh n)).
Proof.
    split.
    - intros Hmc.
        assert (Hmono : forall (beh : behavior State) (n : nat),
                    util_tts F beh n -> util_tts (F \land L) beh n).
        { intros beh n. apply (util_tts_mono F (F \land L) beh n).
            intros c HF. exact (proj2 (Hmc c) HF). }
        split; [| exact Hmono].
        intros beh HC. apply (proj1 (Hmc beh)).
        intros n. exact (Hmono beh n (HC n)).
    - intros [Hsafe Hcompl] beh. split.
        + intros HC. apply (Hsafe beh). intros n.
            exact (util_tts_mono (F \land L) F beh n
                       (fun c HFL => property_implies_closure F c (proj1 HFL))
                       (HC n)).
        + intros HF n.
            exact (Hcompl beh n (property_implies_closure F beh HF n)).
Qed.

#[local] Lemma util_tts_closure {State : Type} (F : property State)
        (beh : behavior State) (n : nat) :
    util_tts (util_closure F) beh n <-> util_tts F beh n.
Proof.
    split.
    - apply (util_tts_mono (util_closure F) F beh n). intros c HC. exact HC.
    - apply (util_tts_mono F (util_closure F) beh n). intros c HF.
        exact (property_implies_closure (util_closure F) c
                   (property_implies_closure F c HF)).
Qed.

#[local] Lemma util_tts_downward {State : Type} (F : property State)
        (beh : behavior State) (m n : nat) :
    m <= n -> util_tts F beh n -> util_tts F beh m.
Proof.
    intros Hmn [Hn | [c [HF Hag]]]; [left; lia | right].
    exists c. split; [exact HF | intros i Hi; apply Hag; lia].
Qed.

#[local] Definition util_trunc {State : Type} (beh : behavior State)
        (m : nat) : behavior State :=
    fun i => beh (Nat.min i m).

#[local] Lemma util_trunc_agree {State : Type} (beh : behavior State)
        (m i : nat) :
    i < S m -> util_trunc beh m i = beh i.
Proof.
    intros Hi. unfold util_trunc. rewrite (Nat.min_l i m); [reflexivity | lia].
Qed.

#[local] Lemma util_trunc_plus {State V : Type} (F : property State)
        (v : State -> V) (beh : behavior State) (m : nat) :
    util_tts F beh m ->
        util_plus_operator (util_closure F) v (util_trunc beh m).
Proof.
    intros HF. right. exists m. split.
    - intros k Hk. unfold util_trunc.
        rewrite (Nat.min_r k m Hk), (Nat.min_r (S k) m) by lia. reflexivity.
    - apply (proj2 (util_tts_closure F (util_trunc beh m) m)).
        apply (util_tts_agree F beh (util_trunc beh m) m); [| exact HF].
        intros i Hi. symmetry. apply util_trunc_agree. lia.
Qed.

#[local] Lemma util_tts_freeze {State : Type} (F : property State)
        (beh : behavior State) (m : nat) :
    util_stuttering_closed F ->
        util_tts F beh (S m) -> util_closure F (util_trunc beh m).
Proof.
    intros Hsc [Habs | [d [HF Hag]]]; [discriminate Habs |].
    intros p. right. exists (util_stutter_at d m p). split.
    - exact (Hsc d _ (stuttering_equivalent_stutter_at d m p) HF).
    - intros i Hi. unfold util_stutter_at, util_trunc.
        destruct (Nat.leb_spec i m) as [Him | Him].
        + rewrite (Nat.min_l i m Him). exact (Hag i (le_n_S i m Him)).
        + rewrite (Nat.min_r i m (Nat.lt_le_incl m i Him)).
            destruct (Nat.leb_spec i (m + p)); [| lia].
            exact (Hag m (Nat.lt_succ_diag_r m)).
Qed.

#[local] Lemma util_prefix_induction {State : Type} (E : property State)
        (E_ M_ : nat -> property State) (b : behavior State) :
    util_stuttering_closed E ->
    (forall (i : nat) (c : behavior State),
        util_closure E c /\ (forall j : nat, util_closure (M_ j) c) ->
            E_ i c) ->
    (forall m k : nat,
        util_tts (E_ k) b m -> util_closure (M_ k) (util_trunc b m)) ->
    forall m : nat, util_tts E b m -> forall j : nat, util_tts (E_ j) b m.
Proof.
    intros HscE Hyp1 Hstep m.
    induction m as [| m IH]; intros HEm j; [left; reflexivity |].
    right. exists (util_trunc b m). split.
    - apply (Hyp1 j (util_trunc b m)).
        split; [exact (util_tts_freeze E b m HscE HEm) |].
        intros k. apply (Hstep m k).
        exact (IH (util_tts_downward E b m (S m) (Nat.le_succ_diag_r m) HEm) k).
    - intros i Hi. apply util_trunc_agree. exact Hi.
Qed.

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
            valid ((\A j \st (util_closure (M j)))
                \impl (E i))) ->
    (* 2. (a) *)
    (forall i : nat,
            valid (((util_plus_operator (util_closure (E i)) v) \land (util_closure (Ml i)))
                \impl (util_closure (M i)))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((Ml i) \land (\A j \st ((\lift0 (j < i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\A i \st Ml i)
        \impl (\A i \st M i)).
Proof.
    intros Hstut Hyp1 Hyp2a Hyp2b beh HMl.
    assert (HCMl : forall j : nat, util_closure (Ml j) beh)
        by (intros j; exact (property_implies_closure (Ml j) beh (HMl j))).
    assert (HE : forall n i : nat, util_tts (E i) beh n).
    { intros n i.
        refine (util_prefix_induction (\lift0 True) E M beh _ _ _ n
                    (property_implies_closure (\lift0 True) beh I n) i).
        - intros b c _ Hb. exact Hb.
        - intros k b [_ HC]. exact (Hyp1 k b HC).
        - intros m k HEk. apply (Hyp2a k (util_trunc beh m)).
            split; [exact (util_trunc_plus (E k) v beh m HEk) |].
            exact (util_tts_freeze (Ml k) beh m (Hstut k) (HCMl k (S m))). }
    assert (HC : forall j : nat, util_closure (M j) beh).
    { intros j. apply (Hyp2a j beh). split; [| exact (HCMl j)].
        left. intros n. exact (HE n j). }
    intros i. induction (Nat.lt_wf_0 i) as [i _ IH].
    exact (Hyp2b i beh (conj (Hyp1 i beh HC) (conj (HMl i) IH))).
Qed.

(* Not from refs *)
(* Acyclic form of the `Decomposition` theorem with strengthening of hypothesis 
   (1.) by replacing `util_closure (M j)` with `M j` *)
Theorem Decomposition0 (E Ml M : nat -> prop) :
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j \st ((\lift0 (j < i)) \impl (M j)))
                \impl (E i))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((Ml i) \land (\A j \st ((\lift0 (j < i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\A i \st Ml i) \impl (\A i \st M i)).
Proof.
    intros Hyp1 Hyp2 beh HMl i.
    induction (Nat.lt_wf_0 i) as [i _ IH].
    exact (Hyp2 i beh (conj (Hyp1 i beh IH) (conj (HMl i) IH))).
Qed.

(* Acyclic composition of `M0` and `M1` where `M1` depends on the specification 
   of `M0` (and not the implementation `Ml0` of `M0`). *)
(* Not from refs *)
#[local] Example ex_01 (Ml0 M0 Ml1 M1 : prop) :
    valid (Ml0  \impl  M0)  ->
        valid ((M0 \land Ml1)  \impl  M1)  ->
            valid ((Ml0 \land Ml1)  \impl  (M0 \land M1)).
Proof.
    intros H0 H1 beh [HMl0 HMl1].
    assert (HM0 : M0 beh) by exact (H0 beh HMl0).
    split; [exact HM0 | exact (H1 beh (conj HM0 HMl1))].
Qed.

(* Not from refs *)
(* Acyclic form of the `Decomposition` theorem with structure defined over
   `dep`endency relation (`dep i j` reads "j depends on i" or "i before j")
   (cf. Decomposition0). *)
Corollary Decomposition1 (dep : nat -> nat -> Prop) (E Ml M : nat -> prop) :
    well_founded dep -> (* The `dep` relation is acyclic and well-founded *)
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j \st ((\lift0 (dep j i)) \impl (M j)))
                \impl (E i))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land ((Ml i) \land (\A j \st ((\lift0 (dep j i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid ((\A i \st Ml i) \impl (\A i \st M i)).
Proof.
    intros Hwf Hyp1 Hyp2 beh HMl i.
    induction (Hwf i) as [i _ IH].
    exact (Hyp2 i beh (conj (Hyp1 i beh IH) (conj (HMl i) IH))).
Qed.

(* Not from refs *)
(* Refinement form of the `Decomposition` theorem (cf.
   Decomposition1). *)
Corollary Decomposition2 {State2 : Type} (r : State -> State2 -> Prop) (E : nat -> property State2) (Ml : nat -> property State) (M : nat -> property State2) :
    (* If... *)
    (* 1. *)
    (forall i : nat,
            valid ((\A j \st ((\lift0 (j < i)) \impl (M j)))
                \impl (E i))) ->
    (* 2. (b) *)
    (forall i : nat,
            valid (((E i) \land (((Ml i) \with0 r) \land (\A j \st ((\lift0 (j < i)) \impl (M j)))))
                \impl (M i))) ->
    (* ...then *)
    valid (((\A i \st Ml i) \with0 r) \impl (\A i \st M i)).
Proof.
    intros Hyp1 Hyp2 beh [c [Hsc HMl]] i.
    induction (Nat.lt_wf_0 i) as [i _ IH].
    apply (Hyp2 i beh). split; [exact (Hyp1 i beh IH) |].
    split; [exists c; split; [exact Hsc | exact (HMl i)] | exact IH].
Qed.

(* Ref: SCP Theorem 8.8 (Composition Theorem) *)
Theorem Composition {V : Type} (v : State -> V) (E M : prop) (E_ M_ : nat -> prop) :
    util_stuttering_closed E  ->
    (forall j : nat,
            util_stuttering_closed (M_ j))  ->
    (* If... *)
    (* 1. *)
    valid (\A i \st (((util_closure E) \land (\A j \st (util_closure (M_ j))))
        \impl (E_ i))) ->
    (* 2. (a) *)
    valid (((util_plus_operator (util_closure E) v) \land (\A j \st (util_closure (M_ j))))
        \impl (util_closure M)) ->
    (* 2. (b) *)
    valid ((E \land (\A j \st M_ j))
        \impl M) ->
    (* ...then *)
    valid ((\A j \st (util_plus_arrow (E_ j) (M_ j)))
        \impl (util_plus_arrow E M)).
Proof.
    intros HscE HscM Hyp1 Hyp2a Hyp2b beh Hspec.
    assert (HQ : forall m : nat,
                util_tts E beh m -> forall j : nat, util_tts (E_ j) beh m).
    { apply (util_prefix_induction E E_ M_ beh HscE (fun i c => Hyp1 c i)).
        intros m k HEk.
        exact (util_tts_freeze (M_ k) beh m (HscM k) (proj2 (Hspec k) m HEk)). }
    split.
    - intros HE.
        assert (HCE : util_closure E beh)
            by exact (property_implies_closure E beh HE).
        assert (HCall : forall j : nat, util_closure (M_ j) beh).
        { intros j p. destruct p as [| p]; [left; reflexivity |].
            exact (proj2 (Hspec j) p (HQ p (HCE p) j)). }
        apply (Hyp2b beh). split; [exact HE |].
        intros j. exact (proj1 (Hspec j) (Hyp1 beh j (conj HCE HCall))).
    - intros n HEn.
        assert (HCM : util_closure M (util_trunc beh n)).
        { apply (Hyp2a (util_trunc beh n)).
            split; [exact (util_trunc_plus E v beh n HEn) |].
            intros k. apply (util_tts_freeze (M_ k) beh n (HscM k)).
            exact (proj2 (Hspec k) n (HQ n HEn k)). }
        apply (util_tts_agree M (util_trunc beh n) beh (S n));
            [| exact (HCM (S n))].
        intros i Hi. apply util_trunc_agree. exact Hi.
Qed.

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
    intros HscE HscMl Hsafe Hyp_a Hyp_b beh Hspec.
    pose (E_ := fun j : nat => match j with 0 => E | _ => \lift0 True end).
    pose (M_ := fun j : nat => match j with 0 => Ml | _ => \lift0 True end).
    refine (Composition v E M E_ M_ HscE _ _ _ _ beh _).
    - intros [| j]; [exact HscMl | intros b c _ Hb; exact Hb].
    - intros b [| j] [HCE HCall]; [exact (Hsafe b HCE) | exact I].
    - intros b [Hplus HCall]. apply (Hyp_a b). split; [| exact (HCall 0)].
        destruct Hplus as [HCE | [k [Hfrz HEk]]].
        + left. exact (Hsafe b HCE).
        + right. exists k.
            split; [exact Hfrz | exact (proj1 (util_tts_closure E b k) HEk)].
    - intros b [HE Hall]. exact (Hyp_b b (conj HE (Hall 0))).
    - intros [| j]; [exact Hspec |].
        split; [intros _; exact I |].
        intros n _. right. exists beh.
        split; [exact I | intros i _; reflexivity].
Qed.

(* Not from refs *)
(* Acyclic form of the `Composition` theorem with strengthening of hypothesis
   (1.) by replacing `util_closure E` with `E` and `util_closure (M_ j)` with
   `M_ j` *)
Theorem Composition0 (E M : prop) (E_ M_ : nat -> prop) :
    (* If... *)
    (* 1. *)
    valid (\A i \st ((E \land (\A j \st ((\lift0 (j < i)) \impl (M_ j))))
        \impl (E_ i))) ->
    (* 2. (b) *)
    valid ((E \land (\A j \st M_ j))
        \impl M) ->
    (* ...then *)
    valid ((\A j \st ((E_ j) \impl (M_ j)))
        \impl (E \impl M)).
Proof.
    intros Hyp1 Hyp2 beh Hspec HE.
    apply (Hyp2 beh). split; [exact HE |].
    intros i. induction (Nat.lt_wf_0 i) as [i _ IH].
    exact (Hspec i (Hyp1 beh i (conj HE IH))).
Qed.

(* Ref: "Conjoining Specifications" Theorem 2 (General Decomposition Theorem) *)
(* The hypothesis "v is a tuple of variables including all the free variables of
   Mi" ("Conjoining Specifications", Theorem 2) is omitted. Instead, as
   suggested in SCP, "The theorem does not [need to] make any assumption about
   v". *)
(* The definition adds `(\A j \st ((\lift0 (j < i)) \impl (M_ j)))` to hypothesis
   (2) b as is done in `Decomposition` (SCP, Theorem 8.7) but missing from
   Theorem 2. *)
Theorem GeneralDecomposition {V : Type} (v : State -> V) (E : prop) (E_ Ml_ M_ : nat -> prop) :
    util_stuttering_closed E  ->
    (forall i : nat,
            util_stuttering_closed (Ml_ i))  ->
    (* If... *)
    (* (1) *)
    (forall i : nat,
            valid (((util_closure E) \land (\A j \st (util_closure (M_ j))))
                \impl (E_ i))) ->
    (* (2) (a) *)
    (forall i : nat,
            valid (((util_plus_operator (util_closure (E_ i)) v) \land (util_closure (Ml_ i)))
                \impl (util_closure (M_ i)))) ->
    (* (2) (b) *)
    (forall i : nat,
            valid (((E_ i) \land ((Ml_ i) \land (\A j \st ((\lift0 (j < i)) \impl (M_ j)))))
                \impl (M_ i))) ->
    (* ...then *)
    (* (a) *)
    valid (((util_plus_operator (util_closure E) v) \land (\A j \st (util_closure (Ml_ j))))
        \impl (\A j \st (util_closure (M_ j))))
    (* (b) *)
    /\ valid ((E \land (\A j \st Ml_ j))
        \impl (\A j \st M_ j)).
Proof.
    intros HscE HscMl Hyp1 Hyp2a Hyp2b.
    assert (HQ : forall b : behavior State,
                (forall j : nat, util_closure (Ml_ j) b) ->
                    forall m : nat, util_tts E b m ->
                        forall j : nat, util_tts (E_ j) b m).
    { intros b HMl. apply (util_prefix_induction E E_ M_ b HscE Hyp1).
        intros m k HEk. apply (Hyp2a k (util_trunc b m)).
        split; [exact (util_trunc_plus (E_ k) v b m HEk) |].
        exact (util_tts_freeze (Ml_ k) b m (HscMl k) (HMl k (S m))). }
    split.
    - intros b [Hplus HMl] j.
        apply (Hyp2a j b). split; [| exact (HMl j)].
        destruct Hplus as [HCE | [k [Hfrz HEk]]].
        + left. intros m. exact (HQ b HMl m (HCE m) j).
        + right. exists k. split; [exact Hfrz |].
            apply (proj2 (util_tts_closure (E_ j) b k)).
            exact (HQ b HMl k (proj1 (util_tts_closure E b k) HEk) j).
    - intros b [HE HMl].
        assert (HCMl : forall j : nat, util_closure (Ml_ j) b)
            by (intros j; exact (property_implies_closure (Ml_ j) b (HMl j))).
        assert (HCE : util_closure E b)
            by exact (property_implies_closure E b HE).
        assert (HCall : forall j : nat, util_closure (M_ j) b).
        { intros j. apply (Hyp2a j b). split; [| exact (HCMl j)].
            left. intros m. exact (HQ b HCMl m (HCE m) j). }
        intros j. induction (Nat.lt_wf_0 j) as [j _ IH].
        exact (Hyp2b j b (conj (Hyp1 j b (conj HCE HCall)) (conj (HMl j) IH))).
Qed.

(* Not from refs *)
(* Acyclic form of the `GeneralDecomposition` theorem with strengthening of
   hypothesis (1) by replacing `util_closure E` with `E` and
   `util_closure (M j)` with `M j` *)
Theorem GeneralDecomposition0 (E : prop) (E_ Ml_ M_ : nat -> prop) :
    (* If... *)
    (* (1) *)
    (forall i : nat,
            valid ((E \land (\A j \st ((\lift0 (j < i)) \impl (M_ j))))
                \impl (E_ i))) ->
    (* (2) (b) *)
    (forall i : nat,
            valid (((E_ i) \land ((Ml_ i) \land (\A j \st ((\lift0 (j < i)) \impl (M_ j)))))
                \impl (M_ i))) ->
    (* ...then *)
    (* (b) *)
    valid ((E \land (\A j \st Ml_ j))
        \impl (\A j \st M_ j)).
Proof.
    intros Hyp1 Hyp2b beh [HE HMl] i.
    induction (Nat.lt_wf_0 i) as [i _ IH].
    exact (Hyp2b i beh (conj (Hyp1 i beh (conj HE IH)) (conj (HMl i) IH))).
Qed.

(* Not from refs *)
(* Acyclic form of the `GeneralDecomposition` theorem with structure defined
   over `dep`endency relation (`dep i j` reads "j depends on i" or
   "i before j") (cf. GeneralDecomposition0). *)
Corollary GeneralDecomposition1 (dep : nat -> nat -> Prop) (E : prop) (E_ Ml_ M_ : nat -> prop) :
    well_founded dep -> (* The `dep` relation is acyclic and well-founded *)
    (* If... *)
    (* (1) *)
    (forall i : nat,
            valid ((E \land (\A j \st ((\lift0 (dep j i)) \impl (M_ j))))
                \impl (E_ i))) ->
    (* (2) (b) *)
    (forall i : nat,
            valid (((E_ i) \land ((Ml_ i) \land (\A j \st ((\lift0 (dep j i)) \impl (M_ j)))))
                \impl (M_ i))) ->
    (* ...then *)
    (* (b) *)
    valid ((E \land (\A j \st Ml_ j))
        \impl (\A j \st M_ j)).
Proof.
    intros Hwf Hyp1 Hyp2b beh [HE HMl] i.
    induction (Hwf i) as [i _ IH].
    exact (Hyp2b i beh (conj (Hyp1 i beh (conj HE IH)) (conj (HMl i) IH))).
Qed.

End rules.
