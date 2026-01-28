Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import Coq.Init.Nat.
Import ListNotations.

Open Scope R_scope.

Definition problem_4_pre (l : list R) : Prop := l <> [].

Definition problem_4_spec (l : list R) (mad : R) : Prop :=
  let n := length l in
  let mu := fold_right Rplus 0 l / INR n in
  mad = fold_right (fun x acc => acc + Rabs (x - mu)) 0 l / INR n.

Example problem_4_test : problem_4_spec [10; 10; 10; 10; 9.232092283615625; 10; 10; 10] 0.16797981295908203125.
Proof.
  unfold problem_4_spec.
  (* Replace the mean calculation with the pre-calculated exact value to simplify the goal *)
  replace (fold_right Rplus 0 [10; 10; 10; 10; 9.232092283615625; 10; 10; 10] /
           INR (length [10; 10; 10; 10; 9.232092283615625; 10; 10; 10]))
    with 9.904011535451953125.
  - simpl.
    (* The mean is approx 9.904.
       10 - mean > 0, so Rabs (10 - mean) = 10 - mean.
       9.23... - mean < 0, so Rabs (9.23... - mean) = -(9.23... - mean). *)
    repeat rewrite Rabs_right by lra.
    rewrite Rabs_left by lra.
    lra.
  - (* Prove the mean calculation is correct *)
    simpl.
    lra.
Qed.