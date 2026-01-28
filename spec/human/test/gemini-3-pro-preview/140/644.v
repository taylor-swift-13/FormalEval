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
  由于需要处理连续空格并跳过它们，简单的结构递归可能不够直接。
  这里使用 fuel (gas) 来保证终止性，或者使用更复杂的递归结构。
  鉴于 Coq 的结构递归限制，我们使用 fuel。
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
                  (* More than 2 consecutive spaces (current space + next space) *)
                  (* Replace all consecutive spaces with - *)
                  dash :: fix_spaces_func n (skip_spaces tl2)
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
  Input: "Exxa"
  Output: "Exxa"
*)
Example test_problem_140_exxa : problem_140_spec "Exxa" "Exxa".
Proof.
  (* Unfold the specification to see the equality goal *)
  unfold problem_140_spec.
  
  (* Unfold the function definition *)
  unfold fix_spaces.
  
  (* 
     Use vm_compute to evaluate the string processing functions.
     Since "Exxa" contains no spaces, the logic simply reconstructs the string.
     vm_compute is efficient for calculating the result of fix_spaces_func on concrete inputs.
  *)
  vm_compute.
  
  (* The result of computation is "Exxa" = "Exxa", which is reflexively true. *)
  reflexivity.
Qed.