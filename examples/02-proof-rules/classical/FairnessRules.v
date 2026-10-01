Require Import Classical.
Require Import tulip.tla.TLA.
Require Import tulip.tla.x_Base.

#[local] Open Scope tla_scope.

Section rules.

Context {State : Type}.
#[local] Notation prop := (property State).

(* ========================================================================== *)
(* The proof rules are from (unless otherwise stated):                        *)
(* > Leslie Lamport. 1994. The temporal logic of actions. ACM Trans. Program. *)
(* > Lang. Syst. 16, 3 (May 1994), 872-923.                                   *)
(* > https://doi.org/10.1145/177492.177726                                    *)
(* ========================================================================== *)

(* ========================================================================== *)
(* Additional Rules                                                           *)
(* ========================================================================== *)

(* Comment: these rules are presumably only provable using classical logic's
   `excluded_middle` *)

#[local] Lemma always_p {V : Type} (P Q N : prop) (f : State -> V)
    (beh : behavior State) :
    valid (P \land [N]_f \impl (P ' \lor Q '))
    -> Always (Stutter N f) beh
    -> Always (Not Q) beh
    -> P beh
    -> Always P beh.
Proof.
    intros Hp1 HN HnoQ HPk m. induction m as [| m IH].
    - exact HPk.
    - destruct (Hp1 (util_suffix beh m) (conj IH (HN m))) as [HP' | HQ'].
        + rewrite prime_suffix in HP'. exact HP'.
        + rewrite prime_suffix in HQ'. destruct (HnoQ _ HQ').
Qed.

#[local] Lemma q_of_step {V : Type} (P Q N A : prop) (f : State -> V)
    (beh : behavior State) (m : nat) :
    valid (P \land <<(N \land A)>>_f \impl Q ')
    -> Always (Stutter N f) beh
    -> Always P beh
    -> NonStutter A f (util_suffix beh m)
    -> Q (util_suffix beh (S m)).
Proof.
    intros Hp2 HN HP [HA Hch].
    destruct (HN m) as [HNm | Hunch]; [| destruct (Hch Hunch)].
    pose proof (Hp2 (util_suffix beh m) (conj (HP m) (conj (conj HNm HA) Hch)))
        as HQ.
    rewrite prime_suffix in HQ. exact HQ.
Qed.

#[local] Lemma stutter_of_no_m {Vf Vg : Type} (N M B : prop) (f : State -> Vf)
    (g : State -> Vg) (beh : behavior State) :
    valid (<<(N \land B)>>_f \impl <<M>>_g)
    -> Always (Stutter N f) beh
    -> Always (Not (NonStutter M g)) beh
    -> Always (Stutter (And N (Not B)) f) beh.
Proof.
    intros Hp1 HN HnoM j. apply NNPP. intro Hns. apply Hns.
    destruct (HN j) as [HNj | Hunch]; [left | right; exact Hunch].
    split; [exact HNj |]. intro HB. apply (HnoM j).
    apply (Hp1 (util_suffix beh j)).
    split; [exact (conj HNj HB) |]. intro Hu. apply Hns. right. exact Hu.
Qed.

Lemma WF1 {V : Type} (P Q N A : prop) (f : State -> V) :
    valid (
        P \land [N]_f \impl (P ' \lor Q ')
    )
    /\ valid(
        P \land <<(N \land A)>>_f \impl Q '
    )
    /\ valid(
        P \impl \enabled <<A>>_f
    )
    -> valid(
        (([]([N]_f)) \land (\wf A \sub f))
        \impl
        (P \leadsto Q)
    ).
Proof.
    intros [Hp1 [Hp2 Hp3]] beh [HN HWF] k.
    apply (always_suffix _ _ k) in HN, HWF.
    set (b := util_suffix beh k) in *. intro HPk.
    apply NNPP. intro Hno.
    assert (HnoQ : Always (Not Q) b).
    { intros m HQ. apply Hno. exists m. exact HQ. }
    pose proof (always_p _ _ _ _ _ Hp1 HN HnoQ HPk) as HP.
    assert (HEn : Always (Enabled (NonStutter A f)) b).
    { intro j. exact (Hp3 (util_suffix b j) (HP j)). }
    destruct (always_now _ _ HWF HEn) as [m HA].
    exact (HnoQ _ (q_of_step _ _ _ _ _ _ _ Hp2 HN HP HA)).
Qed.

Lemma WF2 {Vf Vg : Type} (N M A B P F : prop) (f : State -> Vf) (g : State -> Vg) :
    valid (
        <<(N \land B)>>_f \impl <<M>>_g
    )
    /\ valid (
        P \land (P ') \land <<(N \land A)>>_f \land \enabled <<M>>_g \impl B
    )
    /\ valid (
        P \land \enabled <<M>>_g \impl \enabled <<A>>_f
    )
    /\ valid (
        ([]([(N \land (\lnot B))]_f)) \land (\wf A \sub f) \land ([]F) \land (<>([](\enabled <<M>>_g))) \impl (<>([]P))
    )
    -> valid (
        (([]([N]_f)) \land (\wf A \sub f) \land ([]F)) \impl (\wf M \sub g)
    ).
Proof.
    intros [Hp1 [Hp2 [Hp3 Hp4]]] beh [HN [HWF HF]] k.
    apply (always_suffix _ _ k) in HN, HWF, HF.
    set (b := util_suffix beh k) in *. intro HEnM.
    apply NNPP. intro Hno.
    assert (HnoM : Always (Not (NonStutter M g)) b).
    { intros m HM. apply Hno. exists m. exact HM. }
    pose proof (stutter_of_no_m _ _ _ _ _ _ Hp1 HN HnoM) as HNB.
    assert (HEnMk : Eventually (Always (Enabled (NonStutter M g))) b).
    { exists 0. exact HEnM. }
    destruct (Hp4 b (conj HNB (conj HWF (conj HF HEnMk)))) as [d HPd].
    apply (always_suffix _ _ d) in HN, HWF, HEnM, HnoM.
    set (c := util_suffix b d) in *.
    assert (HEnA : Always (Enabled (NonStutter A f)) c).
    { intro j. exact (Hp3 (util_suffix c j) (conj (HPd j) (HEnM j))). }
    destruct (always_now _ _ HWF HEnA) as [m [HA Hch]].
    destruct (HN m) as [HNm | Hunch]; [| destruct (Hch Hunch)].
    apply (HnoM m). apply (Hp1 (util_suffix c m)).
    split; [split; [exact HNm |] | exact Hch].
    apply (Hp2 (util_suffix c m)). split; [exact (HPd m) |].
    split; [rewrite prime_suffix; exact (HPd (S m)) |].
    exact (conj (conj (conj HNm HA) Hch) (HEnM m)).
Qed.

Lemma SF1 {V : Type} (P Q N A F : prop) (f : State -> V) :
    valid(
        (P \land ([N]_f)) \impl ((P ') \lor (Q '))
    )
    /\ valid(
        (P \land (<<(N \land A)>>_f)) \impl (Q ')
    )
    /\ valid(
        (([]P) \land ([]([N]_f)) \land ([]F)) \impl (<>(\enabled (<<A>>_f)))
    )
    -> valid(
        (([]([N]_f)) \land (\sf A \sub f) \land ([]F)) \impl (P \leadsto Q)
    ).
Proof.
    intros [Hp1 [Hp2 Hp3]] beh [HN [HSF HF]] k.
    apply (always_suffix _ _ k) in HN, HSF, HF.
    set (b := util_suffix beh k) in *. intro HPk.
    apply NNPP. intro Hno.
    assert (HnoQ : Always (Not Q) b).
    { intros m HQ. apply Hno. exists m. exact HQ. }
    pose proof (always_p _ _ _ _ _ Hp1 HN HnoQ HPk) as HP.
    assert (HEn : Always (Eventually (Enabled (NonStutter A f))) b).
    { intro j. apply (Hp3 (util_suffix b j)).
        split; [exact (always_suffix _ _ j HP) |].
        split; [exact (always_suffix _ _ j HN) |].
        exact (always_suffix _ _ j HF). }
    destruct (always_now _ _ HSF HEn) as [m HA].
    exact (HnoQ _ (q_of_step _ _ _ _ _ _ _ Hp2 HN HP HA)).
Qed.

Lemma SF2 {Vf Vg : Type} (N M A B P F : prop) (f : State -> Vf) (g : State -> Vg) :
    valid (
        (<<(N \land B)>>_f) \impl (<<M>>_g) 
    )
    /\ valid (
        P \land (P ') \land (<<(N \land A)>>_f) \impl B
    )
    /\ valid (
        P \land (\enabled (<<M>>_g)) \impl (\enabled (<<A>>_f))
    )
    /\ valid (
        (([]([(N \land (\lnot B))]_f)) \land (\sf A \sub f) \land ([]F) \land ([]<>(\enabled (<<M>>_g)))) \impl (<>([]P))
    )
    -> valid (
        (([]([N]_f)) \land (\sf A \sub f) \land ([]F)) \impl (\sf M \sub g)
    ).
Proof.
    intros [Hp1 [Hp2 [Hp3 Hp4]]] beh [HN [HSF HF]] k.
    apply (always_suffix _ _ k) in HN, HSF, HF.
    set (b := util_suffix beh k) in *. intro HEnM.
    apply NNPP. intro Hno.
    assert (HnoM : Always (Not (NonStutter M g)) b).
    { intros m HM. apply Hno. exists m. exact HM. }
    pose proof (stutter_of_no_m _ _ _ _ _ _ Hp1 HN HnoM) as HNB.
    destruct (Hp4 b (conj HNB (conj HSF (conj HF HEnM)))) as [d HPd].
    apply (always_suffix _ _ d) in HN, HSF, HEnM, HnoM.
    set (c := util_suffix b d) in *.
    assert (HEnA : Always (Eventually (Enabled (NonStutter A f))) c).
    { intro j. destruct (HEnM j) as [i HEi]. exists i.
        apply (Hp3 (util_suffix (util_suffix c j) i)).
        split; [exact (always_suffix _ _ j HPd i) | exact HEi]. }
    destruct (always_now _ _ HSF HEnA) as [m [HA Hch]].
    destruct (HN m) as [HNm | Hunch]; [| destruct (Hch Hunch)].
    apply (HnoM m). apply (Hp1 (util_suffix c m)).
    split; [split; [exact HNm |] | exact Hch].
    apply (Hp2 (util_suffix c m)). split; [exact (HPd m) |].
    split; [rewrite prime_suffix; exact (HPd (S m)) |].
    exact (conj (conj HNm HA) Hch).
Qed.

End rules.
