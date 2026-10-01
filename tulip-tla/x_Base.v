Require Export PeanoNat Lia.
Require Export tulip.tla.TLA.

Lemma util_suffix_shift {State : Type} (beh : behavior State) (n m : nat) :
    util_suffix (util_suffix beh n) m = util_suffix beh (n + m).
Proof.
    revert beh. induction n as [| n IH]; intros beh.
    - reflexivity.
    - exact (IH (util_suffix beh 1)).
Qed.

Lemma always_now {State : Type} (F : property State) (beh : behavior State) :
    Always F beh -> F beh.
Proof.
    intros H. exact (H 0).
Qed.

Lemma always_suffix {State : Type} (F : property State) (beh : behavior State) (k : nat) :
    Always F beh -> Always F (util_suffix beh k).
Proof.
    intros H j. rewrite util_suffix_shift. exact (H (k + j)).
Qed.

Lemma always_suffix_le {State : Type} (F : property State) (beh : behavior State) (n : nat) :
    Always F (util_suffix beh n) ->
        forall k : nat, n <= k -> F (util_suffix beh k).
Proof.
    intros H k Hnk. replace k with (n + (k - n)) by lia.
    rewrite <- util_suffix_shift. exact (H (k - n)).
Qed.

Lemma prime_suffix {State : Type} (F : property State) (beh : behavior State) (k : nat) :
    Prime F (util_suffix beh k) = F (util_suffix beh (S k)).
Proof.
    unfold Prime. rewrite util_suffix_shift, Nat.add_1_r. reflexivity.
Qed.

Lemma util_monotone_le (f : nat -> nat) :
    util_monotone f ->
        forall n m : nat, n <= m -> f n <= f m.
Proof.
    intros Hf n m Hnm. induction Hnm as [| m Hnm IH].
    - apply Nat.le_refl.
    - exact (Nat.le_trans _ _ _ IH (Hf m)).
Qed.

Lemma util_monotone_surjective_0 (f : nat -> nat) :
    util_monotone f -> util_surjective f ->
        f 0 = 0.
Proof.
    intros Hm Hs. destruct (Hs 0) as [x Hx].
    pose proof (util_monotone_le f Hm 0 x (Nat.le_0_l x)). lia.
Qed.

Lemma util_monotone_surjective_step (f : nat -> nat) :
    util_monotone f -> util_surjective f ->
        forall n : nat, f (S n) = f n \/ f (S n) = S (f n).
Proof.
    intros Hm Hs n. destruct (Hs (S (f n))) as [x Hx].
    destruct (Nat.le_gt_cases x n) as [Hxn | Hxn].
    - pose proof (util_monotone_le f Hm x n Hxn). lia.
    - pose proof (util_monotone_le f Hm (S n) x Hxn). pose proof (Hm n). lia.
Qed.

Lemma util_monotone_surjective_cross (f : nat -> nat) :
    util_monotone f -> util_surjective f ->
        forall k : nat, exists n : nat, f n = k /\ f (S n) = S k.
Proof.
    intros Hm Hs k. destruct (Hs (S k)) as [x Hx].
    assert (H : k < f x) by lia. clear Hx.
    induction x as [| x IH].
    - rewrite (util_monotone_surjective_0 f Hm Hs) in H. lia.
    - destruct (Nat.le_gt_cases (f x) k) as [Hle | Hgt].
      + exists x.
        destruct (util_monotone_surjective_step f Hm Hs x) as [E | E]; split; lia.
      + exact (IH Hgt).
Qed.

Lemma util_monotone_compose (f g : nat -> nat) :
    util_monotone f -> util_monotone g ->
        util_monotone (fun n : nat => f (g n)).
Proof.
    intros Hf Hg n. exact (util_monotone_le f Hf (g n) (g (S n)) (Hg n)).
Qed.

Lemma util_surjective_compose (f g : nat -> nat) :
    util_surjective f -> util_surjective g ->
        util_surjective (fun n : nat => f (g n)).
Proof.
    intros Hf Hg y. destruct (Hf y) as [x Hx]. destruct (Hg x) as [z Hz].
    exists z. exact (eq_trans (f_equal f Hz) Hx).
Qed.

Lemma stuttering_equivalent0_pointwise {State1 State2 : Type} (R : State1 -> State2 -> Prop) (b : behavior State1) (c : behavior State2) :
    (forall n : nat, R (b n) (c n)) ->
        util_stuttering_equivalent0 R b c.
Proof.
    intros H. exists (fun n => n), (fun n => n). repeat split.
    - intros n. exact (Nat.le_succ_diag_r n).
    - intros n. exact (Nat.le_succ_diag_r n).
    - intros y. exists y. reflexivity.
    - intros y. exists y. reflexivity.
    - exact H.
Qed.

Lemma stuttering_equivalent_pointwise {State : Type} (b c : behavior State) :
    (forall n : nat, b n = c n) ->
        util_stuttering_equivalent b c.
Proof.
    intros H. exact (stuttering_equivalent0_pointwise eq b c H).
Qed.

Lemma stuttering_equivalent_refl {State : Type} (b : behavior State) :
    util_stuttering_equivalent b b.
Proof.
    apply stuttering_equivalent_pointwise. intros n. reflexivity.
Qed.

Lemma stuttering_equivalent0_flip {State1 State2 : Type} (R : State1 -> State2 -> Prop) (b : behavior State1) (c : behavior State2) :
    util_stuttering_equivalent0 R b c ->
        util_stuttering_equivalent0 (fun t s => R s t) c b.
Proof.
    intros [f [g [Hf [Hg [Sf [Sg H]]]]]]. exists g, f. repeat split.
    - exact Hg.
    - exact Hf.
    - exact Sg.
    - exact Sf.
    - exact H.
Qed.

Lemma stuttering_equivalent0_sym {State : Type} (R : State -> State -> Prop) (b c : behavior State) :
    (forall s t : State, R s t -> R t s) ->
        util_stuttering_equivalent0 R b c ->
            util_stuttering_equivalent0 R c b.
Proof.
    intros HR [f [g [Hf [Hg [Sf [Sg H]]]]]]. exists g, f. repeat split.
    - exact Hg.
    - exact Hf.
    - exact Sg.
    - exact Sf.
    - intros n. exact (HR _ _ (H n)).
Qed.

Lemma stuttering_equivalent_sym {State : Type} (b c : behavior State) :
    util_stuttering_equivalent b c ->
        util_stuttering_equivalent c b.
Proof.
    intros H. exact (stuttering_equivalent0_sym eq b c (fun s t E => eq_sym E) H).
Qed.

Lemma stuttering_equivalent_head {State : Type} (b c : behavior State) :
    util_stuttering_equivalent b c ->
        b 0 = c 0.
Proof.
    intros [f [g [Hf [Hg [Sf [Sg H]]]]]]. pose proof (H 0) as H0.
    rewrite (util_monotone_surjective_0 f Hf Sf) in H0.
    rewrite (util_monotone_surjective_0 g Hg Sg) in H0.
    exact H0.
Qed.

Lemma stuttering_equivalent_map {State1 State2 : Type} (r : State1 -> State2) (b c : behavior State1) :
    util_stuttering_equivalent b c ->
        util_stuttering_equivalent (fun n : nat => r (b n)) (fun n : nat => r (c n)).
Proof.
    intros [f [g [Hf [Hg [Sf [Sg H]]]]]]. exists f, g. repeat split.
    - exact Hf.
    - exact Hg.
    - exact Sf.
    - exact Sg.
    - intros n. exact (f_equal r (H n)).
Qed.
