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

Example problem_4_test : problem_4_spec [2.0; 2.4267204433287306] 0.2133602216643653.
Proof.
  unfold problem_4_spec.
  replace (fold_right Rplus 0 [2.0; 2.4267204433287306] / INR (length [2.0; 2.4267204433287306])) with 2.2133602216643653 by (simpl; lra).
  simpl.
  replace (2.4267204433287306 - 2.2133602216643653) with 0.2133602216643653 by lra.
  replace (2.0 - 2.2133602216643653) with (-0.2133602216643653) by lra.
  rewrite Rabs_right; [|lra].
  rewrite Rabs_left1; [|lra].
  lra.
Qed.