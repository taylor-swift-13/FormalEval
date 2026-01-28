(* 导入所需的Coq库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(* 将单个ASCII字符转换为数字 (0-9)，假设输入合法 *)
Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii ("0"%char) in
  n - zero.

(* 辅助函数：将list ascii转换为自然数 *)
Fixpoint list_ascii_to_nat_aux (l : list ascii) (acc : nat) : nat :=
  match l with
  | [] => acc
  | c :: l' => list_ascii_to_nat_aux l' (acc * 10 + char_to_digit c)
  end.

(* 主函数：将list ascii转换为自然数 *)
Definition list_ascii_to_nat (l : list ascii) : nat :=
  list_ascii_to_nat_aux l 0.

(*
 * 规约：Parse_Fraction
 * 描述：将一个由ASCII字符组成的列表解析为一个由分子和分母组成的自然数对。
 *)
Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    num = list_ascii_to_nat num_s /\
    den = list_ascii_to_nat den_s.

(* 约束：x 与 n 均为有效分数串，且分子/分母为正整数 *)
Definition problem_144_pre (x n : string) : Prop :=
  exists nx dx ny dy,
    Parse_Fraction (list_ascii_of_string x) nx dx /\
    Parse_Fraction (list_ascii_of_string n) ny dy /\
    nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0.

(*
 * 规约：problem_144_spec
 * 描述：simplify 函数的逻辑规约
 *)
Definition problem_144_spec (x n : string) (output : bool) : Prop :=
  exists num_x den_x num_n den_n : nat,
    (* 1. 解析输入的 list ascii *)
    Parse_Fraction (list_ascii_of_string x) num_x den_x /\
    Parse_Fraction (list_ascii_of_string n) num_n den_n /\

    (* 2. 根据题目描述，分子和分母都是正整数 *)
    num_x > 0 /\ den_x > 0 /\
    num_n > 0 /\ den_n > 0 /\

    (* 3. 定义核心逻辑：乘积是否为整数 *)
    let product_num := num_x * num_n in
    let product_den := den_x * den_n in
    output = if (product_num mod product_den) =? 0
             then true
             else false.

(* Test case: input = ["3/8"; "8/3"], output = true *)
Example test_simplify_144 : problem_144_spec "3/8" "8/3" true.
Proof.
  unfold problem_144_spec.
  exists 3, 8, 8, 3.
  
  split.
  { (* Parse "3/8" *)
    unfold Parse_Fraction.
    exists (list_ascii_of_string "3"), (list_ascii_of_string "8").
    repeat split; simpl; reflexivity.
  }
  
  split.
  { (* Parse "8/3" *)
    unfold Parse_Fraction.
    exists (list_ascii_of_string "8"), (list_ascii_of_string "3").
    repeat split; simpl; reflexivity.
  }
  
  split. { lia. }
  split. { lia. }
  split. { lia. }
  split. { lia. }
  
  (* Logic check: (3*8) mod (8*3) = 24 mod 24 = 0 *)
  simpl. reflexivity.
Qed.