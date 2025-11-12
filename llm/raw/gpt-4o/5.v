
Require Import List.
Require Import Nat.

Definition intersperse_spec (numbers : list nat) (delimiter : nat) (result : list nat) : Prop :=
  (numbers = [] /\ result = []) \/
  (exists n, exists ns,
    numbers = n :: ns /\
    result = fold_right (fun x acc => x :: delimiter :: acc) [n] ns).
