(* 导入列表和ASCII字符所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.
Open Scope list_scope.

(* 为清晰起见，定义字符常量 *)
Definition space : ascii := " ".
Definition underscore : ascii := "_".
Definition dash : ascii := "-".

(*
  辅助函数: `skip_spaces input`
  移除输入列表的所有前导空格。
*)
Fixpoint skip_spaces (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | c :: tl =>
      if Ascii.ascii_dec c space then
        skip_spaces tl
      else
        l
  end.

(*
  核心函数: `fix_spaces_func input`
  使用 Fixpoint 实现 fix_spaces 逻辑。
  根据题目要求：
  1. 将所有空格替换为下划线。
  2. 如果有超过2个连续空格（即3个或更多），则替换为横杠 '-'。
*)
Fixpoint fix_spaces_func (fuel : nat) (l : list ascii) : list ascii :=
  match fuel with
  | 0 => [] (* Should not happen if fuel is large enough *)
  | S n =>
      match l with
      | [] => []
      | c :: tl =>
          if Ascii.ascii_dec c space then
            match tl with
            | [] => [underscore] (* 结尾单个空格 *)
            | c2 :: tl2 =>
                if Ascii.ascii_dec c2 space then
                  (* 至少有两个连续空格，检查第三个以确定是否超过2个 *)
                  match tl2 with
                  | [] => [underscore; underscore] (* 结尾正好两个空格 *)
                  | c3 :: tl3 =>
                      if Ascii.ascii_dec c3 space then
                        (* 找到第三个空格，满足 > 2 的条件 *)
                        (* 将整个连续空格块替换为 '-'，并跳过剩余空格 *)
                        dash :: fix_spaces_func n (skip_spaces tl3)
                      else
                        (* 只有两个连续空格，不满足 > 2 条件 *)
                        (* 替换为两个下划线 *)
                        underscore :: underscore :: fix_spaces_func n (c3 :: tl3)
                  end
                else
                  (* 单个空格后跟非空格 *)
                  underscore :: fix_spaces_func n tl
            end
          else
            c :: fix_spaces_func n tl
      end
  end.

(* 包装函数，提供足够的 fuel *)
Definition fix_spaces (s : string) : string :=
  let l := list_ascii_of_string s in
  string_of_list_ascii (fix_spaces_func (length l + 1) l).

(* 输入文本任意 *)
Definition problem_140_pre (s : string) : Prop := True.

(*
  程序规约 (Spec)
  它断言输出列表等于 `fix_spaces` 函数对输入列表的应用结果。
*)
Definition problem_140_spec (s : string) (output : string) : Prop :=
  output = fix_spaces s.

(* 
  Test case proof 
  Input: "EEx  a"
  Output: "EEx__a"
*)
Example test_problem_140_eex_a : problem_140_spec "EEx  a" "EEx__a".
Proof.
  (* Unfold the specification to see the equality goal *)
  unfold problem_140_spec.
  
  (* Unfold the function definition *)
  unfold fix_spaces.
  
  (* 
     Use vm_compute to evaluate the string processing functions.
     The logic will process "EEx  a":
     - 'E', 'E', 'x' are kept.
     - Two spaces are encountered. Since 2 is not > 2, they become "__".
     - 'a' is kept.
     Result: "EEx__a".
  *)
  vm_compute.
  
  (* The result of computation is "EEx__a" = "EEx__a", which is reflexively true. *)
  reflexivity.
Qed.