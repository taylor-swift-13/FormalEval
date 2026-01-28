Require Import List.
Require Import ZArith.
Require Import Reals.
Require Import Lra.
Require Import Lia.
Import ListNotations.
Open Scope R_scope.

Definition problem_72_pre (q : list R) (w : Z) : Prop := True.

Definition problem_72_spec (q : list R) (w : Z) (output : bool) : Prop :=
  (output = true <-> (q = rev q) /\ (fold_left (fun acc x => acc + x) q 0%R <= IZR w)).

Example test_problem_72 :
  problem_72_spec [48.77540799744989%R; -48.319352731351685%R; -3.8838243003108204%R; -48.319352731351685%R] 2%Z false.
Proof.
  unfold problem_72_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [Heq _].
    exfalso.
    pose proof (f_equal (fun l => hd 0%R l) Heq) as Hhd.
    simpl in Hhd.
    assert (48.77540799744989%R <> -48.319352731351685%R) by (apply Rgt_not_eq; lra).
    apply H in Hhd.
    exact Hhd.
Qed.