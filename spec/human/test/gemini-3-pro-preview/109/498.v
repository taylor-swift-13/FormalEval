Require Import List ZArith Arith.
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

Example test_move_one_ball : problem_109_spec [50%Z; 49%Z; 48%Z; 47%Z; 46%Z; 45%Z; 44%Z; 43%Z; 42%Z; 41%Z; 40%Z; 39%Z; 38%Z; 37%Z; 36%Z; 35%Z; 34%Z; 33%Z; 32%Z; 31%Z; 30%Z; 29%Z; 28%Z; 27%Z; 26%Z; 25%Z; 24%Z; 23%Z; 22%Z; 21%Z; 20%Z; 19%Z; 18%Z; 17%Z; 16%Z; 15%Z; 14%Z; 13%Z; 12%Z; 11%Z; 10%Z; 9%Z; 8%Z; 7%Z; 6%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z] false.
Proof.
  unfold problem_109_spec.
  unfold move_one_ball_impl.
  vm_compute.
  reflexivity.
Qed.