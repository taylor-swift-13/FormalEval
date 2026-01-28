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
  根据 HumanEval/140:
  - 将所有空格替换为下划线。
  - 如果有超过2个连续空格（即3个或更多），用一个减号替换。
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
            | [] => [underscore] (* Single space at end *)
            | c2 :: tl2 =>
                if Ascii.ascii_dec c2 space then
                  (* We have at least 2 spaces: c and c2 *)
                  match tl2 with
                  | [] => [underscore; underscore] (* Exactly 2 spaces at end *)
                  | c3 :: tl3 =>
                      if Ascii.ascii_dec c3 space then
                         (* We have at least 3 spaces: c, c2, c3 *)
                         (* Replace the sequence of spaces with dash *)
                         dash :: fix_spaces_func n (skip_spaces tl2)
                      else
                         (* Exactly 2 spaces followed by non-space *)
                         underscore :: underscore :: fix_spaces_func n tl2
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
  Input: "  hExampleEthitssxa3eis Ex3ampleEtEhisxa3e  1   EExample"
  Output: "__hExampleEthitssxa3eis_Ex3ampleEtEhisxa3e__1-EExample"
*)
Example test_problem_140_example : problem_140_spec "  hExampleEthitssxa3eis Ex3ampleEtEhisxa3e  1   EExample" "__hExampleEthitssxa3eis_Ex3ampleEtEhisxa3e__1-EExample".
Proof.
  unfold problem_140_spec.
  unfold fix_spaces.
  vm_compute.
  reflexivity.
Qed.