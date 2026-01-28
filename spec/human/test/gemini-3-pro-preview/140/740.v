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
  根据题目要求：如果连续空格数 > 2 (即 >= 3)，替换为 '-'；否则替换为 '_'。
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
            | c2 :: tl2 =>
                if Ascii.ascii_dec c2 space then
                  match tl2 with
                  | c3 :: tl3 =>
                      if Ascii.ascii_dec c3 space then
                        (* 3 or more consecutive spaces: replace with dash and skip rest *)
                        dash :: fix_spaces_func n (skip_spaces tl3)
                      else
                        (* Exactly 2 spaces: replace current with underscore, recurse *)
                        underscore :: fix_spaces_func n tl
                  | [] =>
                      (* Exactly 2 spaces at end: replace current with underscore, recurse *)
                      underscore :: fix_spaces_func n tl
                  end
                else
                  (* Single space: replace with underscore *)
                  underscore :: fix_spaces_func n tl
            | [] =>
                (* Single space at end *)
                [underscore]
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
  Input: "  Big   Exa 1 2 2\nmple	Example   3        "
  Output: "__Big-Exa_1_2_2\nmple	Example-3-"
*)
Definition input_str : string := 
  "  Big   Exa 1 2 2" ++ String (ascii_of_nat 10) ("mple" ++ String (ascii_of_nat 9) "Example   3        ").

Definition output_str : string := 
  "__Big-Exa_1_2_2" ++ String (ascii_of_nat 10) ("mple" ++ String (ascii_of_nat 9) "Example-3-").

Example test_problem_140_example : problem_140_spec input_str output_str.
Proof.
  unfold problem_140_spec.
  unfold fix_spaces.
  unfold input_str, output_str.
  vm_compute.
  reflexivity.
Qed.