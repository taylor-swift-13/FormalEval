(* def double_the_difference(lst):
'''
Given a list of numbers, return the sum of squares of the numbers
in the list that are odd. Ignore numbers that are negative or not integers.

double_the_difference([1, 3, 2, 0]) == 1 + 9 + 0 + 0 = 10
double_the_difference([-1, -2, 0]) == 0
double_the_difference([9, -2]) == 81
double_the_difference([0]) == 0

If the input list is empty, return 0. *)
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

Definition problem_151_pre (l : list Z) : Prop := True.

Definition problem_151_spec (l : list Z) (res : Z) : Prop :=
  res = fold_left (fun acc h => if (Z.leb 0 h) && (Z.odd h)
                          then Z.add acc (Z.mul h h)
                          else acc) l 0.

Example problem_151_test_new :
  problem_151_spec [-5; 7; -11; -14; -16; 19; 24; 25; 26; -28; -29] 1035%Z.
Proof.
  unfold problem_151_spec.
  simpl.
  reflexivity.
Qed.