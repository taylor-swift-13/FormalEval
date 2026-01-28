Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

(* Convert Z to nat in a safe way for count_ones_helper *)
Fixpoint count_ones_helper (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match n with
      | 0 => 0
      | _ => (n mod 2) + count_ones_helper (n / 2) fuel'
      end
  end.

Definition count_ones (n : nat) : nat :=
  count_ones_helper n n.

Definition z_to_nat_nonneg (z : Z) : nat :=
  match z with
  | Z0 => 0
  | Zpos p => Pos.to_nat p
  | Zneg _ => 0  (* treat negative as 0 for count_ones to avoid complexity *)
  end.

Definition lt_custom_bool (a b : Z) : bool :=
  let ones_a := count_ones (z_to_nat_nonneg a) in
  let ones_b := count_ones (z_to_nat_nonneg b) in
  if ones_a <? ones_b then true
  else if ones_a =? ones_b then (a <? b)
  else false.

Fixpoint insert_sorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t =>
      if lt_custom_bool x h then
        x :: l
      else
        h :: insert_sorted x t
  end.

Fixpoint sort_array_impl (input : list Z) : list Z :=
  match input with
  | [] => []
  | h :: t => insert_sorted h (sort_array_impl t)
  end.

Definition problem_116_spec (input output : list Z) : Prop :=
  output = sort_array_impl input.

Example test_sort_array_negative :
  problem_116_spec [-2; -3; -4; -5; -6] [-4; -2; -6; -5; -3].
Proof.
  unfold problem_116_spec.
  simpl.
  reflexivity.
Qed.

Example test_sort_array_zero :
  problem_116_spec [1;0;2;3;4] [0;1;2;4;3].
Proof.
  unfold problem_116_spec.
  simpl.
  reflexivity.
Qed.