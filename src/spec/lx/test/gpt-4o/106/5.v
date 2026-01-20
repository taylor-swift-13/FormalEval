Require Import Nat.
Require Import List.
Import ListNotations.

Fixpoint factorial (i : nat) : nat :=
  match i with
  | 0 => 1
  | S i' => i * factorial i'
  end.

Fixpoint sum_1_to_n (i : nat) : nat :=
  match i with
  | 0 => 0
  | S i' => i + sum_1_to_n i'
  end.

Definition f_spec (n : nat) (l : list nat) : Prop :=
  l = map (fun i =>
             let problem_index := i + 1 in
             if even problem_index then
               factorial problem_index
             else
               sum_1_to_n problem_index)
          (seq 0 n).

Example f_test_0 :
  f_spec 0 [].
Proof.
  unfold f_spec.
  simpl.
  reflexivity.
Qed.