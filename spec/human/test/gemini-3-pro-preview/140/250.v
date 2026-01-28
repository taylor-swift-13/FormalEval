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
  根据测试用例推断：
  - 单个空格 -> "_"
  - 两个空格 -> "__"
  - 三个及以上空格 -> "-"
*)
Fixpoint fix_spaces_func (fuel : nat) (l : list ascii) : list ascii :=
  match fuel with
  | 0 => []
  | S n =>
      match l with
      | [] => []
      | c :: tl =>
          if Ascii.ascii_dec c space then
            match tl with
            | [] => [underscore]
            | c2 :: tl2 =>
                if Ascii.ascii_dec c2 space then
                   (* 至少两个空格，检查第三个 *)
                   match tl2 with
                   | [] => [underscore; underscore]
                   | c3 :: tl3 =>
                       if Ascii.ascii_dec c3 space then
                         (* 至少三个空格 -> "-" *)
                         dash :: fix_spaces_func n (skip_spaces tl3)
                       else
                         (* 正好两个空格 -> "__" *)
                         underscore :: underscore :: fix_spaces_func n tl2
                   end
                else
                  (* 单个空格 -> "_" *)
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
  Input: "---a-a  ExampleE  Expample   2  3c---"
  Output: "---a-a__ExampleE__Expample-2__3c---"
*)
Example test_problem_140_example : problem_140_spec "---a-a  ExampleE  Expample   2  3c---" "---a-a__ExampleE__Expample-2__3c---".
Proof.
  unfold problem_140_spec.
  unfold fix_spaces.
  vm_compute.
  reflexivity.
Qed.