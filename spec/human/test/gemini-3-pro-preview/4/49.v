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

Example problem_4_test : problem_4_spec [-1; -2; 5; 9.232092283615625; 4.556069003616063] 3.72610580595707008.
Proof.
  unfold problem_4_spec.
  (* Simplify the mean calculation term first *)
  replace (fold_right Rplus 0 [-1; -2; 5; 9.232092283615625; 4.556069003616063] /
           INR (length [-1; -2; 5; 9.232092283615625; 4.556069003616063]))
    with 3.1576322574463376.
  - simpl.
    (* Resolve absolute values based on the calculated mean *)
    replace (Rabs (-1 - 3.1576322574463376)) with (3.1576322574463376 - (-1)) by (rewrite Rabs_left1; lra).
    replace (Rabs (-2 - 3.1576322574463376)) with (3.1576322574463376 - (-2)) by (rewrite Rabs_left1; lra).
    replace (Rabs (5 - 3.1576322574463376)) with (5 - 3.1576322574463376) by (rewrite Rabs_right; lra).
    replace (Rabs (9.232092283615625 - 3.1576322574463376)) with (9.232092283615625 - 3.1576322574463376) by (rewrite Rabs_right; lra).
    replace (Rabs (4.556069003616063 - 3.1576322574463376)) with (4.556069003616063 - 3.1576322574463376) by (rewrite Rabs_right; lra).
    
    (* Final arithmetic verification *)
    lra.
  - (* Proof that the mean is correct *)
    simpl.
    lra.
Qed.