(* 引入所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(* 定义 '(' 和 ')' 的 ASCII 表示 *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(* 辅助函数：将 ASCII 列表转换为字符串 *)
Definition string_of_list_ascii (l : list ascii) : string :=
  fold_right String EmptyString l.

(*
  规约 1: IsBalanced(s)
  使用一个辅助递归函数，其中 count 代表当前未闭合的左括号数。
*)
Fixpoint IsBalanced_aux (s : string) (count : nat) : Prop :=
  match s with
  | EmptyString => count = 0
  | String h t =>
    if ascii_dec h lparen then
      IsBalanced_aux t (S count)
    else if ascii_dec h rparen then
      match count with
      | 0 => False (* 右括号比左括号多，不平衡 *)
      | S n' => IsBalanced_aux t n'
      end
    else
      IsBalanced_aux t count (* 忽略其他字符 *)
  end.

Definition IsBalanced (s : string) : Prop :=
  IsBalanced_aux s 0.

(*
  辅助函数: 移除列表中的空格
*)
Fixpoint remove_spaces (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String h t =>
    if ascii_dec h space then
      remove_spaces t
    else
      String h (remove_spaces t)
  end.

(*
  辅助断言: 检查一个字符是否为括号或空格
  直接使用等式，其类型为 Prop
*)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

(*
  辅助函数: 检查字符串中的所有字符是否满足属性 P
*)
Fixpoint ForallChars (P : ascii -> Prop) (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String h t => P h /\ ForallChars P t
  end.

(*
  实现函数: separate_paren_groups_impl
*)
Fixpoint separate_paren_groups_aux (s : string) (count : nat) (current : list ascii) (acc : list string) : list string :=
  match s with
  | EmptyString => 
    match current with
    | [] => acc
    | _ => acc ++ [string_of_list_ascii (List.rev current)]
    end
  | String h t =>
    if ascii_dec h lparen then
      separate_paren_groups_aux t (S count) (h :: current) acc
    else if ascii_dec h rparen then
      match count with
      | 0 => acc
      | S n' =>
        let new_current := h :: current in
        if Nat.eqb n' 0 then
          separate_paren_groups_aux t n' [] (acc ++ [string_of_list_ascii (List.rev new_current)])
        else
          separate_paren_groups_aux t n' new_current acc
      end
    else if ascii_dec h space then
      separate_paren_groups_aux t count current acc
    else
      separate_paren_groups_aux t count (h :: current) acc
  end.

Definition separate_paren_groups_impl (input : string) : list string :=
  separate_paren_groups_aux (remove_spaces input) 0 [] [].

(*
  最终的程序规约: separate_paren_groups_spec(input, output)
*)
Definition problem_1_spec (input : string) (output : list string) : Prop :=
  output = separate_paren_groups_impl input.

(* 测试用例证明 *)
Example test_separate_paren_groups : 
  problem_1_spec "((( ) ((( )) () (( ))))) (((( )) )) (( ))" 
                ["((()((())()(()))))"; "(((())))"; "(())"].
Proof.
  unfold problem_1_spec.
  unfold separate_paren_groups_impl.
  simpl.
  reflexivity.
Qed.