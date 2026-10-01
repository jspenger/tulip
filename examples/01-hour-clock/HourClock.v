Require Import PeanoNat.
Require Import tulip.tla.TLA.
Require Import tulip.tla.x_Closed.
Require Import ZifyNat.

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
    Record State := Build_State { hour : nat }.
    #[local] Notation prop := (property State).
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

#[local] Lemma hc_state_eq (s s' : HC.State) :
    HC.hour s = HC.hour s' -> s = s'.
Proof.
    destruct s as [h], s' as [h']. cbn. intro H. rewrite H. reflexivity.
Qed.

#[local] Lemma hc_step (beh : behavior HC.State) (k : nat) :
    ([HC.Next]_ HC.vars) (util_suffix beh k) <->
    (HC.hour (beh (S k)) = HC.hour (beh k) mod 12 + 1
        \/ HC.hour (beh (S k)) = HC.hour (beh k)).
Proof.
    unfold Stutter, Or, HC.Next, Unchanged, Lift2, util_suffix, HC.vars.
    rewrite Nat.add_0_r, Nat.add_1_r.
    split; intros [H | H].
    - left. exact H.
    - right. rewrite H. reflexivity.
    - left. exact H.
    - right. apply hc_state_eq. symmetry. exact H.
Qed.

Theorem hc_impl_type_ok :
    valid (
        HC.Spec \impl Type_OK
    ).
Proof.
    (* The proof is left as an exercise for the reader ;-) *)
    intros beh [HInit HNext] k.
    unfold Lift1, util_suffix. rewrite Nat.add_0_r.
    induction k as [| k IH].
    - exact HInit.
    - destruct (proj1 (hc_step beh k) (HNext k)) as [H | H]; rewrite H.
        + lia.
        + exact IH.
Qed.

Theorem hc_impl_incr_ok :
    valid (
        HC.Spec \impl Incr_OK
    ).
Proof.
    intros beh [_ HNext] k.
    unfold Lift2, util_suffix. rewrite Nat.add_0_r, Nat.add_1_r.
    destruct (proj1 (hc_step beh k) (HNext k)) as [H | H]; rewrite H.
    - destruct (HC.hour (beh k)) as [| n]; [exact I |].
        do 12 (destruct n as [| n]; [right; reflexivity |]). exact I.
    - destruct (HC.hour (beh k)) as [| n]; [exact I |].
        do 12 (destruct n as [| n]; [left; reflexivity |]). exact I.
Qed.

(* ========================================================================== *)
(* Safety props imply hc: valid ((Type_OK \land Incr_OK) \impl HC.Spec)       *)
(* ========================================================================== *)

Theorem safety_impl_hc :
    valid (
        (Type_OK \land Incr_OK) \impl HC.Spec
    ).
Proof.
    intros beh [HT HI]. split; [exact (HT 0) |]. intro k.
    apply (proj2 (hc_step beh k)).
    specialize (HT k). unfold Lift1, util_suffix in HT.
    rewrite Nat.add_0_r in HT.
    specialize (HI k). unfold Lift2, util_suffix in HI.
    rewrite Nat.add_0_r, Nat.add_1_r in HI.
    revert HT HI. destruct (HC.hour (beh k)) as [| n]; intros HT HI; [lia |].
    do 12 (destruct n as [| n];
        [destruct HI as [HI | HI]; [right | left]; exact HI |]).
    lia.
Qed.

(* ========================================================================== *)
(* Liveness                                                                   *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Liveness: The hour clock visits every hour (1..12) infinitely often        *)
(* ========================================================================== *)

Definition HC_Is_Live : property HC.State :=
    \A x \in { x : nat | 1 <= x <= 12 } \st (
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
    intro Hv.
    assert (Hspec : HC.Spec (fun _ => HC.Build_State 1)).
    { split.
        - unfold HC.Init, Lift1. cbn. lia.
        - intro k. right. reflexivity. }
    assert (Hx : 1 <= 2 <= 12) by lia.
    destruct (Hv _ Hspec (exist _ 2 Hx) 0) as [j Hj].
    discriminate Hj.
Qed.

(* ========================================================================== *)
(* Fair hour clock is live: valid ((HC.Spec \land F) \impl HC_Is_Live)        *)
(* ========================================================================== *)

Definition F : property HC.State :=
    \wf HC.Next \sub HC.vars.

#[local] Lemma hc_adv_neq (h : nat) : h mod 12 + 1 <> h.
Proof.
    lia.
Qed.

#[local] Lemma hc_enabled (beh : behavior HC.State) :
    (\enabled << HC.Next >>_ HC.vars) beh.
Proof.
    exists (fun i => match i with
        | 0 => beh 0
        | S _ => HC.Build_State (HC.hour (beh 0) mod 12 + 1)
        end).
    split; [reflexivity |]. split; [reflexivity |].
    intro Hc. apply (hc_adv_neq (HC.hour (beh 0))).
    exact (f_equal HC.hour (eq_sym Hc)).
Qed.

#[local] Lemma hc_advance (beh : behavior HC.State) :
    HC.Spec beh -> F beh ->
    forall k, exists m, k <= m /\ HC.hour (beh m) = HC.hour (beh k) mod 12 + 1.
Proof.
    intros [_ HNext] Hfair k.
    destruct (Hfair k) as [j [Hj _]]; [intro m; apply hc_enabled |].
    rewrite util_suffix_shift in Hj.
    unfold HC.Next, Lift2, util_suffix in Hj.
    rewrite Nat.add_0_r, Nat.add_1_r in Hj.
    revert k Hj. induction j as [| j IH]; intros k Hj.
    - rewrite Nat.add_0_r in Hj. exists (S k). split; [lia | exact Hj].
    - destruct (proj1 (hc_step beh k) (HNext k)) as [H | H].
        + exists (S k). split; [lia | exact H].
        + rewrite Nat.add_succ_r in Hj.
            destruct (IH (S k) Hj) as [m [Hm Hhm]].
            exists m. rewrite <- H. split; [lia | exact Hhm].
Qed.

#[local] Lemma hc_advance_n (beh : behavior HC.State) :
    HC.Spec beh -> F beh ->
    forall n k, exists m,
        k <= m /\ HC.hour (beh m) = (HC.hour (beh k) + n) mod 12 + 1.
Proof.
    intros Hspec Hfair n. induction n as [| n IH]; intro k.
    - rewrite Nat.add_0_r. exact (hc_advance beh Hspec Hfair k).
    - destruct (IH k) as [m [Hm Hhm]].
        destruct (hc_advance beh Hspec Hfair m) as [m' [Hm' Hhm']].
        exists m'. split; [lia |].
        rewrite Hhm', Hhm. lia.
Qed.

Theorem fair_hc_impl_live :
    valid (
        (HC.Spec \land F) \impl HC_Is_Live
    ).
Proof.
    intros beh [Hspec Hfair] [x Hx] k.
    pose proof (hc_impl_type_ok beh Hspec k) as Hh.
    unfold Lift1, util_suffix in Hh. rewrite Nat.add_0_r in Hh.
    destruct (hc_advance_n beh Hspec Hfair (x + 11 - HC.hour (beh k)) k)
        as [m [Hm Hhm]].
    exists (m - k). rewrite util_suffix_shift. unfold Lift1, util_suffix. cbn.
    replace (k + (m - k) + 0) with m by lia. rewrite Hhm. lia.
Qed.

(* ========================================================================== *)
(* Refinemenet                                                                *)
(* ========================================================================== *)

(* ========================================================================== *)
(* The hour-minute clock                                                      *)
(* ========================================================================== *)

Module HMC.
    Record State := Build_State { hour : nat ; minute : nat }.
    #[local] Notation prop := (property State).
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
        \wf HMC.Next \sub HMC.vars.
End HMC.

(* ========================================================================== *)
(* Refinement: valid ((HMC.Spec \with r) \impl HC.Spec)                       *)
(* ========================================================================== *)

Definition r (s : HMC.State) : HC.State := 
    HC.Build_State (HMC.hour s).

#[local] Lemma hmc_step (beh : behavior HMC.State) (k : nat) :
    ([HMC.Next]_ HMC.vars) (util_suffix beh k) <->
    (HMC.minute (beh k) < 59
        /\ HMC.minute (beh (S k)) = HMC.minute (beh k) + 1
        /\ HMC.hour (beh (S k)) = HMC.hour (beh k))
    \/ (59 <= HMC.minute (beh k)
        /\ HMC.minute (beh (S k)) = 0
        /\ HMC.hour (beh (S k)) = HMC.hour (beh k) mod 12 + 1)
    \/ beh k = beh (S k).
Proof.
    unfold Stutter, Or, HMC.Next, Unchanged, Lift2, util_suffix, HMC.vars.
    rewrite Nat.add_0_r, (Nat.add_1_r k).
    destruct (Nat.ltb_spec (HMC.minute (beh k)) 59); intuition lia.
Qed.

Theorem hmc_refines_hc : 
    valid (
        (HMC.Spec \with r) \impl HC.Spec
    ).
Proof.
    intros beh [beh1 [Heq [HInit HNext]]].
    apply (and_stuttering_closed _ _ (lift1_stuttering_closed _)
        (always_stutter_stuttering_closed _ _ (lift2_reads _)) _ _ Heq).
    split; [exact (proj1 HInit) |]. intro k. apply (proj2 (hc_step _ k)).
    destruct (proj1 (hmc_step beh1 k) (HNext k))
        as [[_ [_ H]] | [[_ [_ H]] | H]].
    - right. exact H.
    - left. exact H.
    - right. exact (f_equal HMC.hour (eq_sym H)).
Qed.

#[local] Definition hmc_of (beh : behavior HC.State) (n : nat) : HMC.State :=
    HMC.Build_State (HC.hour (beh (n / 60)))
        (if HC.hour (beh (S (n / 60))) =? HC.hour (beh (n / 60))
            then 0 else n mod 60).

#[local] Lemma hmc_of_epoch (beh : behavior HC.State) (q : nat) :
    hmc_of beh (60 * q) = HMC.Build_State (HC.hour (beh q)) 0.
Proof.
    unfold hmc_of. replace (60 * q / 60) with q by lia.
    replace (60 * q mod 60) with 0 by lia.
    destruct (HC.hour (beh (S q)) =? HC.hour (beh q)); reflexivity.
Qed.

#[local] Lemma hmc_of_equiv (beh : behavior HC.State) :
    util_stuttering_equivalent (fun n => r (hmc_of beh n)) beh.
Proof.
    apply stuttering_equivalent_sym.
    apply (stuttering_equivalent_expand _ _ (fun n => n / 60)).
    - intro n. cbn beta. lia.
    - intro q. exists (60 * q). cbn beta. lia.
    - intro n. apply hc_state_eq. reflexivity.
Qed.

#[local] Lemma hmc_of_spec (beh : behavior HC.State) :
    HC.Spec beh -> HMC.Spec (hmc_of beh).
Proof.
    intros [HInit HNext]. split.
    - split; [exact HInit |]. unfold hmc_of. cbn.
        destruct (HC.hour (beh 1) =? HC.hour (beh 0)); lia.
    - intro n. apply (proj2 (hmc_step _ n)).
        destruct (Nat.lt_ge_cases (n mod 60) 59) as [Hm | Hm].
        + unfold hmc_of. cbn [HMC.hour HMC.minute].
            replace (S n / 60) with (n / 60) by lia.
            replace (S n mod 60) with (n mod 60 + 1) by lia.
            destruct (HC.hour (beh (S (n / 60))) =? HC.hour (beh (n / 60))).
            * right. right. reflexivity.
            * left. split; [exact Hm | split; reflexivity].
        + replace (S n) with (60 * S (n / 60)) by lia. rewrite hmc_of_epoch.
            unfold hmc_of. cbn [HMC.hour HMC.minute].
            destruct (proj1 (hc_step beh (n / 60)) (HNext (n / 60)))
                as [H | H]; rewrite H.
            * rewrite (proj2 (Nat.eqb_neq _ _) (hc_adv_neq _)).
                right. left. split; [exact Hm | split; reflexivity].
            * rewrite Nat.eqb_refl. right. right. reflexivity.
Qed.

Theorem hc_refines_hmc : 
    valid (
        HC.Spec \impl (HMC.Spec \with r)
    ).
Proof.
    intros beh Hspec. exists (hmc_of beh).
    split; [exact (hmc_of_equiv beh) | exact (hmc_of_spec beh Hspec)].
Qed.

Theorem hmc_equiv_hc : 
    valid (
        (HMC.Spec \with r) \equiv HC.Spec
    ).
Proof.
    intro beh. split; [exact (hmc_refines_hc beh) | exact (hc_refines_hmc beh)].
Qed.

(* ========================================================================== *)
(* Refinement with fairness                                                   *)
(* ========================================================================== *)

#[local] Lemma hc_nonstutter (beh : behavior HC.State) (k : nat) :
    (<< HC.Next >>_ HC.vars) (util_suffix beh k) <->
    HC.hour (beh (S k)) = HC.hour (beh k) mod 12 + 1.
Proof.
    unfold NonStutter, And, Not, HC.Next, Unchanged, Lift2, util_suffix,
        HC.vars.
    rewrite Nat.add_0_r, (Nat.add_1_r k).
    split; [intros [H _]; exact H |]. intro H. split; [exact H |].
    intro Hc. rewrite Hc in H. exact (hc_adv_neq _ (eq_sym H)).
Qed.

#[local] Lemma hmc_enabled (beh : behavior HMC.State) :
    (\enabled << HMC.Next >>_ HMC.vars) beh.
Proof.
    exists (fun i => match i with
        | 0 => beh 0
        | S _ => if HMC.minute (beh 0) <? 59
            then HMC.Build_State (HMC.hour (beh 0)) (HMC.minute (beh 0) + 1)
            else HMC.Build_State (HMC.hour (beh 0) mod 12 + 1) 0
        end).
    split; [reflexivity |].
    unfold NonStutter, And, Not, HMC.Next, Unchanged, Lift2, HMC.vars.
    destruct (Nat.ltb_spec (HMC.minute (beh 0)) 59);
        cbn [HMC.hour HMC.minute]; (split; [split; reflexivity | intro Hc]).
    - apply (f_equal HMC.minute) in Hc. cbn [HMC.minute] in Hc. lia.
    - apply (hc_adv_neq (HMC.hour (beh 0))).
        exact (f_equal HMC.hour (eq_sym Hc)).
Qed.

#[local] Lemma hmc_walk (beh : behavior HMC.State) :
    ([] [HMC.Next]_ HMC.vars) beh ->
    forall j k, (exists m, k <= m
        /\ HMC.hour (beh (S m)) = HMC.hour (beh m) mod 12 + 1)
        \/ HMC.minute (beh k) <= HMC.minute (beh (k + j)).
Proof.
    intros HNext j k. induction j as [| j IH].
    - right. rewrite Nat.add_0_r. apply le_n.
    - destruct IH as [IH | IH]; [left; exact IH |]. rewrite Nat.add_succ_r.
        destruct (proj1 (hmc_step beh (k + j)) (HNext (k + j)))
            as [[_ [H _]] | [[_ [_ H]] | H]].
        + right. rewrite H. lia.
        + left. exists (k + j). split; [lia | exact H].
        + right. rewrite <- H. exact IH.
Qed.

#[local] Lemma hmc_hour_change (beh : behavior HMC.State) :
    HMC.Spec beh -> HMC.F beh ->
    forall d k, 59 - HMC.minute (beh k) < d -> exists m, k <= m
        /\ HMC.hour (beh (S m)) = HMC.hour (beh m) mod 12 + 1.
Proof.
    intros [_ HNext] Hfair d. induction d as [| d IH]; intros k Hd; [lia |].
    destruct (Hfair k) as [j [_ Hj]]; [intro i; apply hmc_enabled |].
    rewrite util_suffix_shift in Hj.
    unfold Not, Unchanged, Lift2, util_suffix, HMC.vars in Hj.
    rewrite Nat.add_0_r, Nat.add_1_r in Hj.
    destruct (hmc_walk beh HNext j k) as [Hw | Hw]; [exact Hw |].
    destruct (proj1 (hmc_step beh (k + j)) (HNext (k + j)))
        as [[Hlt [Hm _]] | [[_ [_ H]] | H]].
    - destruct (IH (S (k + j))) as [m [Hkm Hc]]; [lia |].
        exists m. split; [lia | exact Hc].
    - exists (k + j). split; [lia | exact H].
    - destruct (Hj H).
Qed.

Theorem fair_hmc_refines_fair_hc : 
    valid (
        ((HMC.Spec \land HMC.F) \with r) \impl (HC.Spec \land F)
    ).
Proof.
    intros beh [beh1 [Heq [Hspec Hfair]]]. split.
    - apply hmc_refines_hc. exists beh1. split; [exact Heq | exact Hspec].
    - apply (weak_fairness_stuttering_closed _ _ (lift2_reads _) _ _ Heq).
        intros k _.
        destruct (hmc_hour_change beh1 Hspec Hfair _ k (Nat.lt_succ_diag_r _))
            as [m [Hkm Hm]].
        exists (m - k). rewrite util_suffix_shift.
        replace (k + (m - k)) with m by lia.
        exact (proj2 (hc_nonstutter (fun n => r (beh1 n)) m) Hm).
Qed.

#[local] Lemma hmc_of_turn (beh : behavior HC.State) (q : nat) :
    HC.hour (beh (S q)) = HC.hour (beh q) mod 12 + 1 ->
    (<< HMC.Next >>_ HMC.vars) (util_suffix (hmc_of beh) (60 * q + 59)).
Proof.
    intro Hq.
    unfold NonStutter, And, Not, HMC.Next, Unchanged, Lift2, util_suffix,
        HMC.vars.
    rewrite Nat.add_0_r. replace (60 * q + 59 + 1) with (60 * S q) by lia.
    rewrite hmc_of_epoch. unfold hmc_of.
    replace ((60 * q + 59) / 60) with q by lia.
    replace ((60 * q + 59) mod 60) with 59 by lia.
    rewrite Hq, (proj2 (Nat.eqb_neq _ _) (hc_adv_neq _)).
    split; [split; reflexivity | discriminate].
Qed.

Theorem fair_hc_refines_fair_hmc : 
    valid (
        (HC.Spec \land F) \impl ((HMC.Spec \land HMC.F) \with r)
    ).
Proof.
    intros beh [Hspec Hfair]. exists (hmc_of beh).
    split; [exact (hmc_of_equiv beh) |].
    split; [exact (hmc_of_spec beh Hspec) |].
    intros n _. destruct (Hfair n) as [j Hj]; [intro i; apply hc_enabled |].
    rewrite util_suffix_shift in Hj.
    exists (60 * (n + j) + 59 - n). rewrite util_suffix_shift.
    replace (n + (60 * (n + j) + 59 - n)) with (60 * (n + j) + 59) by lia.
    exact (hmc_of_turn beh _ (proj1 (hc_nonstutter beh _) Hj)).
Qed.

Theorem fair_hmc_equiv_fair_hc : 
    valid (
        ((HMC.Spec \land HMC.F) \with r) \equiv (HC.Spec \land F)
    ).
Proof.
    intro beh. split.
    - exact (fair_hmc_refines_fair_hc beh).
    - exact (fair_hc_refines_fair_hmc beh).
Qed.
