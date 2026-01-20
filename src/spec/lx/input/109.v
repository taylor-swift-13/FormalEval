(* We have an array 'arr' of N integers arr[1], arr[2], ..., arr[N].The
numbers in the array will be randomly ordered. Your task is to determine if
it is possible to get an array sorted in non-decreasing order by performing
the following operation on the given array:
You are allowed to perform right shift operation any number of times.

One right shift operation means shifting all elements of the array by one
position in the right direction. The last element of the array will be moved to
the starting position in the array i.e. 0th index.

If it is possible to obtain the sorted array by performing the above operation
then return True else return False.
If the given array is empty then return True.

Note: The given list is guaranteed to have unique elements.

For Example:

move_one_ball([3, 4, 5, 1, 2])==>True
Explanation: By performin 2 right shift operations, non-decreasing order can
be achieved for the given array.
move_one_ball([3, 5, 4, 1, 2])==>False
Explanation:It is not possible to get non-decreasing order for the given
array by performing any number of right shift operations. *)

(* 导入列表、整数和自然数所需的基础库 *)
Require Import List ZArith Arith.
Require Import Coq.Sorting.Sorted.
Open Scope Z_scope.
Import ListNotations.


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


Definition move_one_ball_spec (arr : list Z) (result : bool) : Prop :=
  match arr with
  (* 情况1: 如果输入列表为空，规约要求结果必须为 true。*)
  | [] => result = true
  (* 情况2: 如果列表非空，规约要求结果为 true 当且仅当
   *         存在某个移位次数 n，使得列表在经过 n 次右移后是排序的。*)
  | _ :: _ => result = true <-> (exists n : nat, Sorted Z.le (n_shifts n arr))
  end.