Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_ones_pos (p : positive) : Z :=
  match p with
  | xI p' => 1 + count_ones_pos p'
  | xO p' => count_ones_pos p'
  | xH => 1
  end.

Definition count_ones (n : Z) : Z :=
  match n with
  | Z0 => 0
  | Zpos p => count_ones_pos p
  | Zneg p => count_ones_pos p
  end.

Definition lt_custom (a b : Z) : Prop :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ a < b).

Definition lt_custom_bool (a b : Z) : bool :=
  let ones_a := count_ones a in
  let ones_b := count_ones b in
  if ones_a <? ones_b then true
  else if ones_a =? ones_b then a <? b
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

Example test_problem_116 :
  problem_116_spec [111111%Z; 1111111%Z; 11111111%Z; 111111111%Z; 1111111111%Z; 111111%Z; 1111%Z; 111%Z; 11111%Z; 111111111%Z; 1111111%Z] 
                   [111%Z; 1111%Z; 111111%Z; 111111%Z; 11111%Z; 1111111%Z; 1111111%Z; 11111111%Z; 1111111111%Z; 111111111%Z; 111111111%Z].
Proof.
  unfold problem_116_spec.
  reflexivity.
Qed.