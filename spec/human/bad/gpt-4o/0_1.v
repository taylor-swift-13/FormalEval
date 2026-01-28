Require Import List Reals Psatz.
Import ListNotations.
Open Scope R_scope.

Definition problem_0_pre(threshold : R): Prop :=
  threshold >= 0.

Definition problem_0_spec (numbers : list R) (threshold : R) (output : bool): Prop :=
  (exists (i j : nat) (x y : R),
    i <> j /\
    Nat.lt i (length numbers) /\
    Nat.lt j (length numbers) /\
    nth i numbers 0%R = x /\
    nth j numbers 0%R = y /\
    Rabs (x - y) <= threshold) <->
    output = true.

Example test_case_0 :
  problem_0_spec [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] 0.3 true.
Proof.
  unfold problem_0_spec.
  split.
  - intros [i [j [x [y [H_neq [H_i [H_j [H_x [H_y H_close]]]]]]]]].
    simpl in *.
    (* We will enumerate possible pairs (i, j) and check if they satisfy the condition *)
    assert (H_cases: (i = 1 /\ j = 5) \/ (i = 5 /\ j = 1)).
    {
      (* Check for pairs that satisfy Rabs(x - y) <= 0.3 *)
      destruct i; destruct j; simpl in *; try (right; left); try (left; split; reflexivity); try lia; try firstorder.
      all: simpl in *; try lra.
    }
    destruct H_cases as [[H_i1 H_j5] | [H_i5 H_j1]].
    + subst. simpl in *. rewrite Rabs_right in H_close; lra.
    + subst. simpl in *. rewrite Rabs_left in H_close; lra.
  - exists 1, 5, 2.0, 2.2.
    simpl; repeat split; try lia.
    + intros H_eq. inversion H_eq.
    + apply Rabs_left; lra.
Qed.