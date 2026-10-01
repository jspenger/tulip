Require Export tulip.tla.x_Base.

#[local] Definition util_walk_step (p q : nat -> nat) (nm : nat * nat) : nat * nat :=
    match nm with
    | (n, m) =>
        if Nat.eq_dec (p (S n)) (p n) then (S n, m)
        else if Nat.eq_dec (q (S m)) (q m) then (n, S m)
        else (S n, S m)
    end.

#[local] Fixpoint util_walk (p q : nat -> nat) (i : nat) : nat * nat :=
    match i with
    | 0 => (0, 0)
    | S i => util_walk_step p q (util_walk p q i)
    end.

#[local] Lemma util_walk_step_facts (p q : nat -> nat) (i : nat) :
    fst (util_walk p q i) <= fst (util_walk p q (S i))
    /\ fst (util_walk p q (S i)) <= S (fst (util_walk p q i))
    /\ snd (util_walk p q i) <= snd (util_walk p q (S i))
    /\ snd (util_walk p q (S i)) <= S (snd (util_walk p q i))
    /\ S (fst (util_walk p q i) + snd (util_walk p q i))
        <= fst (util_walk p q (S i)) + snd (util_walk p q (S i)).
Proof.
    simpl. destruct (util_walk p q i) as [n m]. unfold util_walk_step.
    destruct (Nat.eq_dec (p (S n)) (p n)); [simpl; lia |].
    destruct (Nat.eq_dec (q (S m)) (q m)); simpl; lia.
Qed.

#[local] Lemma util_walk_sum (p q : nat -> nat) (i : nat) :
    i <= fst (util_walk p q i) + snd (util_walk p q i).
Proof.
    induction i as [| i IH].
    - exact (Nat.le_0_l _).
    - destruct (util_walk_step_facts p q i) as [_ [_ [_ [_ H]]]]. lia.
Qed.

#[local] Lemma util_walk_inv (p q : nat -> nat) :
    util_monotone p -> util_surjective p -> util_monotone q -> util_surjective q ->
        forall i : nat, p (fst (util_walk p q i)) = q (snd (util_walk p q i)).
Proof.
    intros Hp Sp Hq Sq i. induction i as [| i IH].
    - simpl. rewrite (util_monotone_surjective_0 p Hp Sp).
      rewrite (util_monotone_surjective_0 q Hq Sq). reflexivity.
    - simpl. destruct (util_walk p q i) as [n m]. simpl in IH. unfold util_walk_step.
      destruct (Nat.eq_dec (p (S n)) (p n)) as [E1 | E1]; [simpl; lia |].
      destruct (Nat.eq_dec (q (S m)) (q m)) as [E2 | E2]; [simpl; lia |].
      simpl.
      destruct (util_monotone_surjective_step p Hp Sp n) as [H1 | H1]; [contradiction |].
      destruct (util_monotone_surjective_step q Hq Sq m) as [H2 | H2]; [contradiction |].
      lia.
Qed.

#[local] Lemma util_walk_cofinal (p q a b : nat -> nat) :
    (forall i : nat, i <= a i + b i) ->
    (forall i : nat, p (a i) = q (b i)) ->
    util_monotone p -> util_monotone q -> util_surjective q ->
        forall N : nat, exists i : nat, N <= a i.
Proof.
    intros Hsum Hinv Hp Hq Sq N. destruct (Sq (S (p N))) as [X HX].
    exists (N + X).
    destruct (Nat.le_gt_cases N (a (N + X))) as [H | H]; [exact H |].
    exfalso.
    pose proof (Hsum (N + X)). pose proof (Hinv (N + X)).
    pose proof (util_monotone_le p Hp (a (N + X)) N (Nat.lt_le_incl _ _ H)).
    assert (HX' : X <= b (N + X)) by lia.
    pose proof (util_monotone_le q Hq X (b (N + X)) HX').
    lia.
Qed.

#[local] Lemma util_surjective_of_steps (s : nat -> nat) :
    s 0 = 0 ->
    (forall i : nat, s (S i) <= S (s i)) ->
    (forall N : nat, exists i : nat, N <= s i) ->
        util_surjective s.
Proof.
    intros H0 Hs Hu k. destruct (Hu k) as [i Hi]. revert Hi. revert k.
    induction i as [| i IH]; intros k Hk.
    - exists 0. lia.
    - destruct (Nat.le_gt_cases k (s i)) as [Hle | Hgt].
      + exact (IH k Hle).
      + exists (S i). pose proof (Hs i). lia.
Qed.

#[local] Lemma util_walk_merge (p q : nat -> nat) :
    util_monotone p -> util_surjective p -> util_monotone q -> util_surjective q ->
        exists n m : nat -> nat,
            util_monotone n /\ util_monotone m
            /\ util_surjective n /\ util_surjective m
            /\ (forall i : nat, p (n i) = q (m i)).
Proof.
    intros Hp Sp Hq Sq.
    pose proof (util_walk_inv p q Hp Sp Hq Sq) as Hinv.
    assert (Hsum : forall i : nat, i <= snd (util_walk p q i) + fst (util_walk p q i)).
    { intros i. pose proof (util_walk_sum p q i). lia. }
    assert (Hinv' : forall i : nat, q (snd (util_walk p q i)) = p (fst (util_walk p q i))).
    { intros i. symmetry. exact (Hinv i). }
    exists (fun i => fst (util_walk p q i)), (fun i => snd (util_walk p q i)).
    repeat split.
    - intros i. destruct (util_walk_step_facts p q i) as [H _]. exact H.
    - intros i. destruct (util_walk_step_facts p q i) as [_ [_ [H _]]]. exact H.
    - apply util_surjective_of_steps.
      + reflexivity.
      + intros i. destruct (util_walk_step_facts p q i) as [_ [H _]]. exact H.
      + exact (util_walk_cofinal p q (fun i => fst (util_walk p q i))
            (fun i => snd (util_walk p q i)) (util_walk_sum p q) Hinv Hp Hq Sq).
    - apply util_surjective_of_steps.
      + reflexivity.
      + intros i. destruct (util_walk_step_facts p q i) as [_ [_ [_ [H _]]]]. exact H.
      + exact (util_walk_cofinal q p (fun i => snd (util_walk p q i))
            (fun i => fst (util_walk p q i)) Hsum Hinv' Hq Hp Sp).
    - exact Hinv.
Qed.

Lemma stuttering_equivalent0_compose {State1 State2 State3 : Type} (R1 : State1 -> State2 -> Prop) (R2 : State2 -> State3 -> Prop) (a : behavior State1) (b : behavior State2) (c : behavior State3) :
    util_stuttering_equivalent0 R1 a b ->
        util_stuttering_equivalent0 R2 b c ->
            util_stuttering_equivalent0 (fun x z => exists y, R1 x y /\ R2 y z) a c.
Proof.
    intros [f1 [g1 [Hf1 [Hg1 [Sf1 [Sg1 H1]]]]]] [f2 [g2 [Hf2 [Hg2 [Sf2 [Sg2 H2]]]]]].
    destruct (util_walk_merge g1 f2 Hg1 Sg1 Hf2 Sf2) as [n [m [Hn [Hm [Sn [Sm Hnm]]]]]].
    exists (fun i => f1 (n i)), (fun i => g2 (m i)). repeat split.
    - exact (util_monotone_compose f1 n Hf1 Hn).
    - exact (util_monotone_compose g2 m Hg2 Hm).
    - exact (util_surjective_compose f1 n Sf1 Sn).
    - exact (util_surjective_compose g2 m Sg2 Sm).
    - intros i. exists (b (g1 (n i))). split.
      + exact (H1 (n i)).
      + rewrite (Hnm i). exact (H2 (m i)).
Qed.

Lemma stuttering_equivalent0_mono {State1 State2 : Type} (R R' : State1 -> State2 -> Prop) (b : behavior State1) (c : behavior State2) :
    (forall s t, R s t -> R' s t) ->
        util_stuttering_equivalent0 R b c ->
            util_stuttering_equivalent0 R' b c.
Proof.
    intros HR [f [g [Hf [Hg [Sf [Sg H]]]]]]. exists f, g. repeat split.
    - exact Hf.
    - exact Hg.
    - exact Sf.
    - exact Sg.
    - intros n. exact (HR _ _ (H n)).
Qed.

Lemma stuttering_equivalent0_trans {State1 State2 : Type} (R : State1 -> State2 -> Prop) (a : behavior State1) (b c : behavior State2) :
    util_stuttering_equivalent0 R a b ->
        util_stuttering_equivalent b c ->
            util_stuttering_equivalent0 R a c.
Proof.
    intros Hab Hbc.
    apply (stuttering_equivalent0_mono (fun s u => exists t, R s t /\ t = u) R).
    - intros s u [t [Ht E]]. rewrite <- E. exact Ht.
    - exact (stuttering_equivalent0_compose R eq a b c Hab Hbc).
Qed.

Lemma stuttering_equivalent_trans0 {State1 State2 : Type} (R : State1 -> State2 -> Prop) (a b : behavior State1) (c : behavior State2) :
    util_stuttering_equivalent a b ->
        util_stuttering_equivalent0 R b c ->
            util_stuttering_equivalent0 R a c.
Proof.
    intros Hab Hbc.
    apply (stuttering_equivalent0_mono (fun s u => exists t, s = t /\ R t u) R).
    - intros s u [t [E Ht]]. rewrite E. exact Ht.
    - exact (stuttering_equivalent0_compose eq R a b c Hab Hbc).
Qed.

Lemma stuttering_equivalent_trans {State : Type} (a b c : behavior State) :
    util_stuttering_equivalent a b ->
        util_stuttering_equivalent b c ->
            util_stuttering_equivalent a c.
Proof.
    intros Hab Hbc. exact (stuttering_equivalent0_trans eq a b c Hab Hbc).
Qed.

#[local] Lemma util_suffix_sampling (f : nat -> nat) (i : nat) :
    util_monotone f -> util_surjective f ->
        (forall n : nat, f (i + n) - f i <= f (i + S n) - f i)
        /\ (forall y : nat, exists n : nat, f (i + n) - f i = y).
Proof.
    intros Hf Sf. split.
    - intros n. pose proof (Hf (i + n)). rewrite Nat.add_succ_r. lia.
    - intros y. destruct (Sf (f i + y)) as [x Hx].
      destruct (Nat.le_gt_cases i x) as [Hix | Hix].
      + exists (x - i). replace (i + (x - i)) with x by lia. lia.
      + exists 0. pose proof (util_monotone_le f Hf x i (Nat.lt_le_incl _ _ Hix)).
        rewrite Nat.add_0_r. lia.
Qed.

Lemma stuttering_equivalent_suffix {State : Type} (b c : behavior State) :
    util_stuttering_equivalent b c ->
        forall k : nat, exists j : nat,
            util_stuttering_equivalent (util_suffix b j) (util_suffix c k).
Proof.
    intros [f [g [Hf [Hg [Sf [Sg H]]]]]] k. destruct (Sg k) as [i Hi].
    destruct (util_suffix_sampling f i Hf Sf) as [Hf' Sf'].
    destruct (util_suffix_sampling g i Hg Sg) as [Hg' Sg'].
    assert (E : forall n : nat, b (f i + (f (i + n) - f i)) = c (k + (g (i + n) - g i))).
    { intros n.
      pose proof (util_monotone_le f Hf i (i + n) (Nat.le_add_r i n)).
      pose proof (util_monotone_le g Hg i (i + n) (Nat.le_add_r i n)).
      replace (f i + (f (i + n) - f i)) with (f (i + n)) by lia.
      replace (k + (g (i + n) - g i)) with (g (i + n)) by lia.
      exact (H (i + n)). }
    exists (f i), (fun n => f (i + n) - f i), (fun n => g (i + n) - g i). repeat split.
    - exact Hf'.
    - exact Hg'.
    - exact Sf'.
    - exact Sg'.
    - exact E.
Qed.

Lemma stuttering_equivalent_step {State : Type} (b c : behavior State) :
    util_stuttering_equivalent b c ->
        forall k : nat,
            c k = c (S k) \/ (exists j : nat, b j = c k /\ b (S j) = c (S k)).
Proof.
    intros [f [g [Hf [Hg [Sf [Sg H]]]]]] k.
    destruct (util_monotone_surjective_cross g Hg Sg k) as [n [Hn1 Hn2]].
    rewrite <- Hn2, <- Hn1, <- (H n), <- (H (S n)).
    destruct (util_monotone_surjective_step f Hf Sf n) as [E | E].
    - left. rewrite E. reflexivity.
    - right. exists (f n). rewrite E. split; reflexivity.
Qed.

Lemma stuttering_equivalent_expand {State : Type} (b c : behavior State) (f : nat -> nat) :
    util_monotone f -> util_surjective f ->
        (forall n : nat, b (f n) = c n) ->
            util_stuttering_equivalent b c.
Proof.
    intros Hf Sf H. exists f, (fun n => n). repeat split.
    - exact Hf.
    - intros n. exact (Nat.le_succ_diag_r n).
    - exact Sf.
    - intros y. exists y. reflexivity.
    - exact H.
Qed.

Definition util_stutter_at {State : Type} (beh : behavior State) (m k : nat) : behavior State :=
    fun i =>
        if Nat.leb i m then beh i
        else if Nat.leb i (m + k) then beh m
        else beh (i - k).

#[local] Definition util_stutter_map (m k i : nat) : nat :=
    if Nat.leb i m then i else if Nat.leb i (m + k) then m else i - k.

#[local] Lemma util_stutter_map_monotone (m k : nat) :
    util_monotone (util_stutter_map m k).
Proof.
    intros i. unfold util_stutter_map.
    destruct (Nat.leb_spec i m); destruct (Nat.leb_spec (S i) m);
        destruct (Nat.leb_spec i (m + k)); destruct (Nat.leb_spec (S i) (m + k)); lia.
Qed.

#[local] Lemma util_stutter_map_surjective (m k : nat) :
    util_surjective (util_stutter_map m k).
Proof.
    intros y. unfold util_stutter_map.
    destruct (Nat.leb_spec y m) as [Hy | Hy].
    - exists y. destruct (Nat.leb_spec y m); [reflexivity | lia].
    - exists (y + k).
      destruct (Nat.leb_spec (y + k) m); [lia |].
      destruct (Nat.leb_spec (y + k) (m + k)); lia.
Qed.

Lemma stuttering_equivalent_stutter_at {State : Type} (beh : behavior State) (m k : nat) :
    util_stuttering_equivalent beh (util_stutter_at beh m k).
Proof.
    apply (stuttering_equivalent_expand beh (util_stutter_at beh m k) (util_stutter_map m k)).
    - exact (util_stutter_map_monotone m k).
    - exact (util_stutter_map_surjective m k).
    - intros n. unfold util_stutter_at, util_stutter_map.
      destruct (Nat.leb n m); destruct (Nat.leb n (m + k)); reflexivity.
Qed.
