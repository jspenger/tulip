Require Import Coq.Strings.String.
Require Import Classical.
Require Import tulip.tla.TLA.
Require Import tulip.tla.x_Base.
Require Import tulip.examples.proofrules.QuantificationRules.

#[local] Open Scope tla_scope.

(* ========================================================================== *)
(* Quantification                                                             *)
(* ========================================================================== *)

(* Not from refs *)
Lemma FF4 {V : Type} (x : string) (F G : property (State V)) :
    valid (F \impl \AA x : F) -> (* x not free in F *)
        valid ((\AA x : (F \lor G))
            \equiv (F \lor (\AA x : G))).
Proof.
    intros Hfree beh. split.
    - intros HA. apply NNPP. intros Hn. apply Hn. right. intros beh1 Hse.
        destruct (HA beh1 Hse) as [HF | HG].
        + exfalso. apply Hn. left. apply (Hfree beh1 HF).
            apply stuttering_equivalent0_sym; [| exact Hse].
            intros s t Hst y Hy. exact (eq_sym (Hst y Hy)).
        + exact HG.
    - intros [HF | HG] beh1 Hse.
        + left. exact (Hfree beh HF beh1 Hse).
        + right. exact (HG beh1 Hse).
Qed.
