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
  - 单个空格 -> 下划线
  - 两个连续空格 -> 两个下划线 (因为题目要求"多于2个"才变短横线，所以2个按1个处理两次)
  - 多于2个连续空格 (即3个及以上) -> 短横线
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
            | [] => [underscore] (* Single space at end *)
            | c2 :: tl2 =>
                if Ascii.ascii_dec c2 space then
                  (* Check for 3rd space to distinguish between 2 spaces and >2 spaces *)
                  match tl2 with
                  | [] => underscore :: fix_spaces_func n tl (* Exactly 2 spaces at end *)
                  | c3 :: tl3 =>
                      if Ascii.ascii_dec c3 space then
                        (* 3 or more consecutive spaces: replace with dash and skip rest *)
                        dash :: fix_spaces_func n (skip_spaces tl2)
                      else
                        (* Exactly 2 consecutive spaces: treat as separate spaces *)
                        underscore :: fix_spaces_func n tl
                  end
                else
                  (* Single space followed by non-space *)
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
  Input: "Testing     1  2   3"
  Output: "Testing-1__2-3"
*)
Example test_problem_140 : problem_140_spec "Testing     1  2   3" "Testing-1__2-3".
Proof.
  (* Unfold the specification to see the equality goal *)
  unfold problem_140_spec.
  
  (* Unfold the function definition *)
  unfold fix_spaces.
  
  (* 
     Use vm_compute to evaluate the string processing functions.
  *)
  vm_compute.
  
  (* The result of computation matches the expected output. *)
  reflexivity.
Qed.