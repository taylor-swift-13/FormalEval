Require Import ZArith.
Require Import Bool.
Require Import List.
Open Scope Z_scope.

Definition largest_divisor_spec (n d : Z) : Prop :=
  1 < n ->
  1 < d < n /\
  n mod d = 0 /\
  (forall k, 1 < k < n -> n mod k = 0 -> d <= k).

Fixpoint smallest_divisor_from (n : Z) (k limit : nat) : Z :=
  match limit with
  | O => 1%Z
  | S limit' =>
      let zk := Z.of_nat k in
      if (Z.ltb 1 zk) && (Z.ltb zk n) && Z.eqb (n mod zk) 0
      then zk
      else smallest_divisor_from n (S k) limit'
  end.

Definition largest_divisor (n : Z) : Z :=
  smallest_divisor_from n 2%nat (Z.to_nat n).

Definition run (input : list Z) : Z :=
  match input with
  | n :: _ => largest_divisor n
  | _ => 0%Z
  end.

Example test_case_input_3_output_1 :
  run (3%Z :: nil) = 1%Z.
Proof.
  reflexivity.
Qed.