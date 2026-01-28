Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Open Scope Z_scope.
Import ListNotations.

Fixpoint is_sorted_bool (l : list Z) : bool :=
  match l with
  | [] => true
  | [_] => true
  | h1 :: t =>
      match t with
      | [] => true
      | h2 :: t' => if Z.leb h1 h2 then is_sorted_bool t else false
      end
  end.

Definition right_shift (l : list Z) : list Z :=
  match rev l with
  | [] => []
  | hd :: tl => hd :: rev tl
  end.

Fixpoint n_shifts (n : nat) (l : list Z) : list Z :=
  match n with
  | 0%nat => l
  | S n' => right_shift (n_shifts n' l)
  end.

Fixpoint check_all_shifts (arr : list Z) (n : nat) : bool :=
  match n with
  | O => is_sorted_bool arr
  | S n' => orb (is_sorted_bool (n_shifts n arr)) (check_all_shifts arr n')
  end.

Definition move_one_ball_impl (arr : list Z) : bool :=
  match arr with
  | [] => true
  | _ :: _ => check_all_shifts arr (length arr)
  end.

Definition problem_109_pre (arr : list Z) : Prop := NoDup arr.

Definition problem_109_spec (arr : list Z) (result : bool) : Prop :=
  result = move_one_ball_impl arr.

Example problem_109_testcase_1 :
  problem_109_spec [12%Z; 6%Z; 7%Z; 1%Z; 8%Z; 4%Z] false.
Proof.
  unfold problem_109_spec.
  vm_compute.
  reflexivity.
Qed.