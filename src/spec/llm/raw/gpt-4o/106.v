
Require Import List.
Require Import Arith.

Definition factorial (n : nat) : nat :=
  fold_left Nat.mul (seq 1 n) 1.

Definition sum_to_n (n : nat) : nat :=
  fold_left Nat.add (seq 1 n) 0.

Definition f_spec (n : nat) (lst : list nat) : Prop :=
  (n = 0 -> lst = []) /\
  (n = 1 -> lst = [1]) /\
  (n = 2 -> lst = [1; 2]) /\
  (n >= 3 ->
    lst = 
      let fix compute (i : nat) (acc : list nat) :=
          match i with
          | 0 => acc
          | S i' =>
              let value := 
                if Nat.even i 
                then factorial i 
                else sum_to_n i 
              in compute i' (value :: acc)
          end
      in rev (compute n [])).
