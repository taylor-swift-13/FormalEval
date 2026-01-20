Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((n >=? 48)%nat && (n <=? 57)%nat)%bool.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48)%nat.

Fixpoint sum_nums (s : string) (curr : Z) (acc : Z) : Z :=
  match s with
  | EmptyString => acc + curr
  | String c s' =>
      if is_digit c then
        sum_nums s' (curr * 10 + digit_to_Z c) acc
      else
        sum_nums s' 0 (acc + curr)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - sum_nums s 0 0.

Example fruit_distribution_example: fruit_distribution "0 apples and 1 oranges" 8 = 7.
Proof.
  vm_compute.
  reflexivity.
Qed.