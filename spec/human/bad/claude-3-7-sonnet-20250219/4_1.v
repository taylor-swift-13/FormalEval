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

Example example_problem_4 :
  problem_4_spec [1.0;2.0;3.0] (2 / 3).
Proof.
  unfold problem_4_spec.
  simpl.

  (* length 3 *)
  replace (length [1;2;3]) with 3 by reflexivity.
  rewrite INR_3.

  (* sum = 6 *)
  assert (S: fold_right Rplus 0 [1;2;3] = 6) by (simpl; lra).
  rewrite S.

  (* mean mu = 6 / 3 = 2 *)
  replace (6 / 3) with 2 by lra.

  (* sum of absolute differences *)
  assert (A : fold_right (fun x acc => acc + Rabs (x - 2)) 0 [1;2;3] = 2).
  {
    simpl.
    (* |1-2| = 1 *)
    rewrite Rabs_left with (r:=1 - 2).
    - (* |2-2| = 0 *)
      rewrite Rabs_right with (r:=2 - 2).
      + (* |3-2| = 1 *)
        rewrite Rabs_right with (r:=3 - 2).
        * lra.
        * lra.
      + lra.
    - lra.
  }
  rewrite A.

  (* Goal: 2 / 3 = 2 / 3 *)
  lra.
Qed.