Require Import tulip.tla.TLA.
Require Import tulip.tla.x_Stutter.

#[local] Open Scope tla_scope.

Section rules.

Context {State1 State2 : Type}.

(* TODO: Keep only the useful rules... *)

(* ========================================================================== *)
(* Utility definitions                                                        *)
(* ========================================================================== *)

(* Not from refs *)
Definition util_inverse (r : State1 -> State2) (s2 : State2) (s1 : State1) : Prop :=
    r s1 = s2.

(* Not from refs *)
Definition util_inverse0 (r : State1 -> State2 -> Prop) (s2 : State2) (s1 : State1) : Prop :=
    r s1 s2.

(* Not from refs *)
Definition util_reflexive (f : State1 -> State1) : Prop :=
    forall s1, f s1 = s1.

(* Not from refs *)
Definition util_reflexive0 (r: State1 -> State1 -> Prop) : Prop :=
    forall s1, r s1 s1.

(* Not from refs *)
Definition util_symmetric (f : State1 -> State1) : Prop :=
    forall s1, f (f s1) = s1.

(* Not from refs *)
Definition util_symmetric0 (r : State1 -> State1 -> Prop) : Prop :=
    forall s1 s2, r s1 s2 -> r s2 s1.

(* Not from refs *)
Definition util_partial_function0 (r : State1 -> State2 -> Prop) : Prop :=
    forall s1 s2 s3, r s1 s2 -> r s1 s3 -> s2 = s3.

(* Not from refs *)
(* The refinement mapping operator `RefinementMapping` but __not__ stuttering
   closed *)
Definition util_with2 {S1 S2 : Type} (f : S1 -> S2) (F : property S1) : property S2 :=
    fun beh2 =>
        exists beh1 : behavior S1,
            (forall n : nat, f (beh1 n) = beh2 n)
            /\ F beh1.

(* Not from refs *)
(* The refinement mapping operator `CoRefinementMapping` but __not__ stuttering
   closed *)
Definition util_co_with2 {S1 S2 : Type} (f : S1 -> S2) (F : property S1) : property S2 :=
    fun beh2 =>
        forall beh1 : behavior S1,
            (forall n : nat, f (beh1 n) = beh2 n)
            -> F beh1.

(* Not from refs *)
(* The refinement mapping operator `RefinementMapping0` but __not__ stuttering
   closed *)
Definition util_with02 {S1 S2 : Type} (r : S1 -> S2 -> Prop) (F : property S1) : property S2 :=
    fun beh2 =>
        exists beh1 : behavior S1,
            (forall n : nat, r (beh1 n) (beh2 n))
            /\ F beh1.

(* Not from refs *)
(* The refinement mapping operator `CoRefinementMapping0` but __not__ stuttering
   closed *)
Definition util_co_with02 {S1 S2 : Type} (r : S1 -> S2 -> Prop) (F : property S1) : property S2 :=
    fun beh2 =>
        forall beh1 : behavior S1,
            (forall n : nat, r (beh1 n) (beh2 n))
            -> F beh1.

(* ========================================================================== *)
(* Utility lemmas                                                             *)
(* ========================================================================== *)

(* Not from refs *)
Lemma AUX1 (Op : property State1 -> property State2) (F G : property State1) :
    (forall F G : property State1, valid (F \impl G) -> valid ((Op F) \impl (Op G))) ->
        valid (Op (F \land G)
            \impl (Op F) \land (Op G)).
Proof.
    intros Hm beh H. split.
    - apply (Hm (F \land G) F); [intros b [HF _]; exact HF | exact H].
    - apply (Hm (F \land G) G); [intros b [_ HG]; exact HG | exact H].
Qed.

(* Not from refs *)
Lemma AUX2 (Op : property State1 -> property State2) (F_ : nat -> property State1) :
    (forall F G : property State1, valid (F \impl G) -> valid ((Op F) \impl (Op G))) ->
        valid (Op (\A i \st F_ i)
            \impl \A i \st Op (F_ i)).
Proof.
    intros Hm beh H i.
    apply (Hm (\A j \st F_ j) (F_ i)); [intros b Hb; exact (Hb i) | exact H].
Qed.

(* ========================================================================== *)
(* Refinement Mapping / 0                                                     *)
(* ========================================================================== *)

(* Note: not from references *)
(* Refinement version of EE1 *)
Lemma RM1 (f : State1 -> State1) (F : property State1) :
    util_reflexive f ->
        valid (F \impl (F \with f)).
Proof.
    intros Hf beh HF. exists beh. split; [| exact HF].
    exact (stuttering_equivalent_pointwise _ beh (fun n => Hf (beh n))).
Qed.

(* Note: not from references *)
(* Refinement version of EE1 *)
Lemma R0M1 (r : State1 -> State1 -> Prop) (F : property State1) :
    util_reflexive0 r ->
        valid (F \impl (F \with0 r)).
Proof.
    intros Hr beh HF. exists beh. split; [| exact HF].
    exact (stuttering_equivalent0_pointwise r beh beh (fun n => Hr (beh n))).
Qed.

(* Note: not from references *)
(* Refinement version of EE2 *)
Lemma RM2 (f: State1 -> State1) (F G : property State1) :
    valid (G \with f \impl G) (* cf. "x not free in G" with "x" as f in EE2 *)
        -> valid (F \impl G)
            -> valid (F \with f \impl G).
Proof.
    intros Hfree HFG beh [c [Hse HF]].
    apply Hfree. exists c. split; [exact Hse | exact (HFG c HF)].
Qed.

(* Note: not from references *)
(* Refinement version of EE2 *)
Lemma R0M2 (r: State1 -> State1 -> Prop) (F G : property State1) :
    valid (G \with0 r \impl G) (* cf. "x not free in G" with "x" as f in EE2 *)
        -> valid (F \impl G)
            -> valid (F \with0 r \impl G).
Proof.
    intros Hfree HFG beh [c [Hse HF]].
    apply Hfree. exists c. split; [exact Hse | exact (HFG c HF)].
Qed.

(* Note: not from references *)
(* Refinement version of EE3 *)
Lemma RM3 (f : State1 -> State2) (F G : property State1) :
    valid (F \impl G)
        -> valid ((F \with f) \impl (G \with f)).
Proof.
    intros HFG beh [c [Hse HF]].
    exists c. split; [exact Hse | exact (HFG c HF)].
Qed.

(* Note: not from references *)
(* Refinement version of EE3 *)
Lemma R0M3 (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid (F \impl G)
        -> valid ((F \with0 r) \impl (G \with0 r)).
Proof.
    intros HFG beh [c [Hse HF]].
    exists c. split; [exact Hse | exact (HFG c HF)].
Qed.

(* Note: not from references *)
Lemma RM4 (f : State1 -> State2) (F G : property State1) :
    util_injective f ->
        util_stuttering_closed G ->
            valid ((F \with f) \impl (G \with f)) ->
                valid (F \impl G).
Proof.
    intros Hinj HGc HFG beh HF.
    destruct (HFG (fun n => f (beh n))) as [c [Hse HG]].
    - exists beh. split; [exact (stuttering_equivalent_refl _) | exact HF].
    - apply (HGc c beh); [| exact HG].
      exact (stuttering_equivalent0_mono _ eq c beh Hinj Hse).
Qed.

(* Not from refs *)
Lemma RM5a (f : State1 -> State2) (F G : property State1) :
    valid (((F \land G) \with f)
        \impl ((F \with f) \land (G \with f))).
Proof.
    exact (AUX1 (RefinementMapping f) F G (RM3 f)).
Qed.

(* Not from refs *)
Lemma RM5b (f : State1 -> State2) (F_ : nat -> property State1) :
    valid (((\A i \st F_ i) \with f)
        \impl (\A i \st (F_ i \with f))).
Proof.
    exact (AUX2 (RefinementMapping f) F_ (RM3 f)).
Qed.

Lemma RM5c (f : State1 -> State2) (F G : property State1) :
    valid (((F \with f) \land (G \cowith f))
        \impl ((F \land G) \with f)).
Proof.
    intros beh [[c [Hse HF]] HG].
    exists c. split; [exact Hse | exact (conj HF (HG c Hse))].
Qed.

(* Not from refs *)
Lemma R0M5a (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid (((F \land G) \with0 r)
        \impl ((F \with0 r) \land (G \with0 r))).
Proof.
    exact (AUX1 (RefinementMapping0 r) F G (R0M3 r)).
Qed.

(* Not from refs *)
Lemma R0M5b (r : State1 -> State2 -> Prop) (F_ : nat -> property State1) :
    valid (((\A i \st F_ i) \with0 r)
        \impl (\A i \st (F_ i \with0 r))).
Proof.
    exact (AUX2 (RefinementMapping0 r) F_ (R0M3 r)).
Qed.

(* Not from refs *)
Lemma R0M5c (r : State1 -> State2 -> Prop) (F G : property State1) :
    valid (((F \with0 r) \land (G \cowith0 r))
        \impl ((F \land G) \with0 r)).
Proof.
    intros beh [[c [Hse HF]] HG].
    exists c. split; [exact Hse | exact (conj HF (HG c Hse))].
Qed.

(* Not from refs *)
Lemma RM6a (r : State1 -> State2) (F : property State2) (G : property State1) :
    util_stuttering_closed F ->
        valid ((((F \with0 (util_inverse r)) \land G) \with r)
            \impl (F \land (G \with r))).
Proof.
    intros HFc beh [c [Hse [[h [Hh HF]] HG]]]. split.
    - apply (HFc h beh); [| exact HF].
      refine (stuttering_equivalent_trans _ _ _ _ Hse).
      apply stuttering_equivalent_sym, (stuttering_equivalent0_flip _ h c Hh).
    - exists c. split; [exact Hse | exact HG].
Qed.

(* Not from refs *)
Lemma R0M6a (f : State1 -> State2 -> Prop) (F : property State2) (G : property State1) :
    util_partial_function0 f ->
        util_stuttering_closed F ->
            valid ((((F \with0 (util_inverse0 f)) \land G) \with0 f)
                \impl (F \land (G \with0 f))).
Proof.
    intros Hf HFc beh [c [Hse [[h [Hh HF]] HG]]]. split.
    - apply (HFc h beh); [| exact HF].
      refine (stuttering_equivalent0_mono _ eq h beh _
          (stuttering_equivalent0_compose _ f h c beh Hh Hse)).
      intros s t [u [Hu Hu']]. exact (Hf u s t Hu Hu').
    - exists c. split; [exact Hse | exact HG].
Qed.

(* Not from refs *)
Lemma RM6b (r : State1 -> State2) (F : property State2) (G : property State1) :
    valid ((F \land (G \with r))
        \impl (((F \with0 (util_inverse r)) \land G) \with r)).
Proof.
    intros beh [HF [c [Hse HG]]]. exists c. split; [exact Hse |].
    split; [| exact HG]. exists beh. split; [| exact HF].
    exact (stuttering_equivalent0_flip (fun s t => r s = t) c beh Hse).
Qed.

(* Not from refs *)
Lemma R0M6b (f : State1 -> State2 -> Prop) (F : property State2) (G : property State1) :
    valid ((F \land (G \with0 f))
        \impl (((F \with0 (util_inverse0 f)) \land G) \with0 f)).
Proof.
    intros beh [HF [c [Hse HG]]]. exists c. split; [exact Hse |].
    split; [| exact HG]. exists beh. split; [| exact HF].
    exact (stuttering_equivalent0_flip f c beh Hse).
Qed.

#[local] Lemma with0_adjunction {S1 S2 : Type} (R : S1 -> S2 -> Prop)
        (F : property S1) (G : property S2) :
    valid ((F \with0 R) \impl G) <->
        valid (F \impl (G \cowith0 (fun t s => R s t))).
Proof.
    split.
    - intros H c HF h Hh. apply H. exists c. split; [| exact HF].
      exact (stuttering_equivalent0_flip _ h c Hh).
    - intros H h [c [Hse HF]].
      exact (H c HF h (stuttering_equivalent0_flip R c h Hse)).
Qed.

(* Not from refs *)
Lemma RM7 (f : State1 -> State2) (F : property State1) (G : property State2) :
    valid (F \with f \impl G) <->
        valid (F \impl (G \cowith0 (util_inverse f))).
Proof.
    exact (with0_adjunction (fun s t => f s = t) F G).
Qed.

(* Not from refs *)
Lemma R0M7 (f : State1 -> State2 -> Prop) (F : property State1) (G : property State2) :
    valid (F \with0 f \impl G) <->
        valid (F \impl (G \cowith0 (util_inverse0 f))).
Proof.
    exact (with0_adjunction f F G).
Qed.

(* Not from refs *)
Lemma RM8 (f : State1 -> State2) (F : property State2) (G : property State1) :
    valid (F \with0 (util_inverse f) \impl G) <->
        valid (F \impl (G \cowith f)).
Proof.
    exact (with0_adjunction (util_inverse f) F G).
Qed.

(* Not from refs *)
Lemma R0M8 (f : State1 -> State2 -> Prop) (F : property State2) (G : property State1) :
    valid (F \with0 (util_inverse0 f) \impl G) <->
        valid (F \impl (G \cowith0 f)).
Proof.
    exact (with0_adjunction (util_inverse0 f) F G).
Qed.

(* Not from refs *)
Lemma RM9 (f : State1 -> State1) (G : property State1) :
    util_symmetric f ->
        valid ((G \with f) \impl G) ->
            valid (G \impl (G \cowith f)).
Proof.
    intros Hf Hfree beh HG c Hse. apply Hfree. exists beh. split; [| exact HG].
    refine (stuttering_equivalent0_sym (fun s t => f s = t) c beh _ Hse).
    intros s t E. rewrite <- E. exact (Hf s).
Qed.

(* Not from refs *)
Lemma R0M9 (r : State1 -> State1 -> Prop) (G : property State1) :
    util_symmetric0 r ->
        valid ((G \with0 r) \impl G) ->
            valid (G \impl (G \cowith0 r)).
Proof.
    intros Hr Hfree beh HG c Hse. apply Hfree. exists beh. split; [| exact HG].
    exact (stuttering_equivalent0_sym r c beh Hr Hse).
Qed.

(* Not from refs *)
Lemma RM10a (f : State1 -> State2) (F : property State1) :
    valid ((util_with2 f F) \impl (F \with f)).
Proof.
    intros beh [c [Hc HF]]. exists c. split; [| exact HF].
    exact (stuttering_equivalent_pointwise _ beh Hc).
Qed.

(* Not from refs *)
Lemma RM10b (f : State1 -> State2) (F : property State1) :
    valid ((F \cowith f) \impl (util_co_with2 f F)).
Proof.
    intros beh H c Hc. exact (H c (stuttering_equivalent_pointwise _ beh Hc)).
Qed.

Lemma RM11a (f : State1 -> State2) (F : property State2) :
    util_stuttering_closed F ->
        valid ((F \with0 (util_inverse f))
            \impl (util_with02 (util_inverse f) F)).
Proof.
    intros HFc beh [h [Hh HF]]. exists (fun n => f (beh n)).
    split; [exact (fun n => eq_refl) |]. apply (HFc h); [| exact HF].
    apply stuttering_equivalent_sym, (stuttering_equivalent0_flip _ h beh Hh).
Qed.

(* Not from refs *)
Lemma RM11b (f : State1 -> State2) (F : property State2) :
    util_stuttering_closed F ->
        valid ((util_co_with02 (util_inverse f) F)
            \impl (F \cowith0 (util_inverse f))).
Proof.
    intros HFc beh H h Hh.
    apply (HFc (fun n => f (beh n)) h (stuttering_equivalent0_flip _ h beh Hh)).
    exact (H _ (fun n => eq_refl)).
Qed.

(* Not from refs *)
Lemma RM12 (f : State1 -> State2) (Bl : property State1) (A B : property State2) :
    util_stuttering_closed A ->
        util_stuttering_closed B ->
            valid (((util_with02 (util_inverse f) A) \land Bl)
                \impl (util_co_with02 (util_inverse f) B)) ->
                    valid ((A \land (Bl \with f)) \impl B).
Proof.
    intros HAc HBc H beh HX.
    refine (proj2 (RM7 f _ B) _ beh (RM6b f A Bl beh HX)).
    intros c [HA HBl].
    exact (RM11b f B HBc c (H c (conj (RM11a f A HAc c HA) HBl))).
Qed.

End rules.
