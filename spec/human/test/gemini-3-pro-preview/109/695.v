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

Example test_move_one_ball : problem_109_spec [11%Z; 4%Z; 7%Z; -1%Z; 8%Z] false.
Proof.
  (* Unfold the specification definition *)
  unfold problem_109_spec.
  
  (* Unfold the implementation definition *)
  unfold move_one_ball_impl.
  
  (* 
     The goal is now to prove:
     false = check_all_shifts [11; 4; 7; -1; 8] (length [11; 4; 7; -1; 8])
     
     Since the list is concrete and finite, we can simply compute the boolean result.
  *)
  vm_compute.
  
  (* The computation reduces the equation to false = false *)
  reflexivity.
Qed.