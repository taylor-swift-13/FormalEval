Require Import List Reals Lra Lia.
Import ListNotations.
Open Scope R_scope.

Definition problem_0_pre(threshold : R): Prop :=
  threshold >= 0.

Definition problem_0_spec (numbers : list R) (threshold : R) (output : bool): Prop :=
  (exists (i j : nat) (x y : R),
    i <> j /\
    Nat.lt i (length numbers) /\
    Nat.lt j (length numbers) /\
    nth i numbers 0 = x /\
    nth j numbers 0 = y /\
    Rabs (x - y) <= threshold) <->
    output = true.

Example test_case_0: problem_0_spec [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] 0.3 true.
Proof.
  unfold problem_0_spec.
  split.
  - (* Existence implies output=true *)
    intros _.
    reflexivity.
  - (* output=true implies Existence *)
    intros _.
    (* We choose indices 2 (value 3.9) and 3 (value 4.0) *)
    (* Their difference is 0.1, which is <= 0.3 *)
    exists 2%nat, 3%nat, 3.9, 4.0.
    repeat split.
    + (* i <> j *)
      lia.
    + (* i < length *)
      simpl. lia.
    + (* j < length *)
      simpl. lia.
    + (* nth 2 ... = 3.9 *)
      simpl. reflexivity.
    + (* nth 3 ... = 4.0 *)
      simpl. reflexivity.
    + (* Rabs (3.9 - 4.0) <= 0.3 *)
      unfold Rabs.
      (* 3.9 - 4.0 = -0.1 *)
      destruct (Rcase_abs (3.9 - 4.0)).
      * (* Case < 0 *)
        lra.
      * (* Case >= 0 *)
        lra.
Qed.