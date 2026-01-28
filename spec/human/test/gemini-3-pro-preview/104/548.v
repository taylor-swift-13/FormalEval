(* 导入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

(* 辅助定义：判断单个数字是否为奇数 *)
Definition is_odd_digit (d : Z) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.

Fixpoint all_digits_odd_list (l : list Z) : Prop :=
  match l with
  | [] => True (* 空列表满足条件 *)
  | h :: t => is_odd_digit h /\ all_digits_odd_list t (* 头部是奇数且尾部也满足条件 *)
  end.

(*
  将 Z 转换为 list Z (使用结构递归 on fuel)
*)

(*
  这是一个使用 "fuel" 技巧的辅助函数。
  - n: 我们要转换的数。
  - fuel: 一个计数器，确保递归会终止。
*)
Fixpoint Z_to_digits_fueled (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => [] (* 燃料耗尽，停止 *)
  | S fuel' => (* 还有燃料，继续 *)
      (* 我们也需要检查 n 是否已经为0 *)
      if Z.eqb n 0 then
        []
      else
        (n mod 10) :: Z_to_digits_fueled (n / 10) fuel'
  end.

(*
  主转换函数。
  使用足够的 "fuel"。对于 Z，我们使用常数 fuel，因为 Z 没有结构递归。
  100 对于实际输入已经足够大。
*)
Definition Z_to_digits (n : Z) : list Z :=
  Z_to_digits_fueled n 100%nat.


Definition has_only_odd_digits (n : Z) : Prop :=
  all_digits_odd_list (Z_to_digits n).

(*
  第四部分: 实现函数
*)

(* 判断数字是否只有奇数字（bool版本） *)
Definition has_only_odd_digits_bool (n : Z) : bool :=
  let digits := Z_to_digits n in
  forallb (fun d => orb (Z.eqb d 1) (orb (Z.eqb d 3) (orb (Z.eqb d 5) (orb (Z.eqb d 7) (Z.eqb d 9))))) digits.

(* 过滤函数 *)
Fixpoint filter_odd_digits (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
      if has_only_odd_digits_bool h then
        h :: filter_odd_digits t
      else
        filter_odd_digits t
  end.

(* 插入排序 *)
Fixpoint insert_sorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t =>
      if Z.leb x h then
        x :: l
      else
        h :: insert_sorted x t
  end.

Fixpoint sort_list (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (sort_list t)
  end.

Definition unique_digits_impl (x : list Z) : list Z :=
  sort_list (filter_odd_digits x).


(* 列表元素均为正整数 *)
Definition problem_104_pre (x : list Z) : Prop := Forall (fun n => n > 0) x.

Definition problem_104_spec (x y : list Z) : Prop :=
  y = unique_digits_impl x.

(* 
  Test case:
  input = [2; 4; 987654321; 8; 10; 14; 16; 18; 20; 16], output = []
*)
Example test_problem_104 : problem_104_spec [2; 4; 987654321; 8; 10; 14; 16; 18; 20; 16] [].
Proof.
  (* Unfold the specification to expose the implementation equality *)
  unfold problem_104_spec.
  
  (* Unfold the implementation detail *)
  unfold unique_digits_impl.
  
  (* 
     Use vm_compute to evaluate the function on the concrete input.
  *)
  vm_compute.
  
  (* The result of evaluation matches the expected output exactly *)
  reflexivity.
Qed.