Require Import List ZArith.
Import ListNotations.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Fixpoint sum_to_n (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => n + sum_to_n n'
  end.

Definition f_spec (n : nat) (result : list nat) : Prop :=
  result = map (fun i => if Nat.even i then factorial i else sum_to_n i) (seq 1 n).

Example test_case_1 : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  (* The goal is to show [1; 2; 6; 24; 15] equals the result of the map function.
     Since all inputs are concrete constants, we can compute the result directly.
     
     Calculation details:
     seq 1 5 = [1; 2; 3; 4; 5]
     
     i = 1 (odd):  sum_to_n 1 = 1
     i = 2 (even): factorial 2 = 2 * 1 = 2
     i = 3 (odd):  sum_to_n 3 = 3 + 2 + 1 = 6
     i = 4 (even): factorial 4 = 4 * 3 * 2 * 1 = 24
     i = 5 (odd):  sum_to_n 5 = 5 + 4 + 3 + 2 + 1 = 15
  *)
  reflexivity.
Qed.