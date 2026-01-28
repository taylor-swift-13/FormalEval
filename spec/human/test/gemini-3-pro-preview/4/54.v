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

Example problem_4_test : problem_4_spec [10; 10; 10; 9.232092283615625] 0.287965393644140625.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [10; 10; 10; 9.232092283615625] / INR (length [10; 10; 10; 9.232092283615625])) 
    with 9.80802307090390625.
  - simpl.
    replace (10 - 9.80802307090390625) with 0.19197692909609375 by lra.
    replace (9.232092283615625 - 9.80802307090390625) with (-0.57593078728828125) by lra.
    replace (Rabs 0.19197692909609375) with 0.19197692909609375 by (rewrite Rabs_right; lra).
    replace (Rabs (-0.57593078728828125)) with 0.57593078728828125 by (rewrite Rabs_left1; lra).
    lra.
  - simpl. lra.
Qed.