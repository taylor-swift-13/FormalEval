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

(* ascii list 转 string 的辅助函数 *)
Fixpoint string_of_list_ascii (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | h :: t => String h (string_of_list_ascii t)
  end.

(* 判断是否平衡 *)
Fixpoint IsBalanced_aux (s : string) (count : nat) : Prop :=
  match s with
  | EmptyString => count = 0
  | String h t =>
    if ascii_dec h lparen then
      IsBalanced_aux t (S count)
    else if ascii_dec h rparen then
      match count with
      | 0 => False
      | S n' => IsBalanced_aux t n'
      end
    else
      IsBalanced_aux t count
  end.

Definition IsBalanced (s : string) : Prop :=
  IsBalanced_aux s 0.

(* 去除空格 *)
Fixpoint remove_spaces (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String h t =>
    if ascii_dec h space then remove_spaces t
    else String h (remove_spaces t)
  end.

(* 字符是否为括号或空格 *)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

(* 字符串中所有字符满足 P *)
Fixpoint ForallChars (P : ascii -> Prop) (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String h t => P h /\ ForallChars P t
  end.

(* 主分割函数 *)
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

(* 规约前提 *)
Definition problem_1_pre (input : string) : Prop :=
  ForallChars is_paren_or_space input /\
  IsBalanced (remove_spaces input).

(* 规约 *)
Definition problem_1_spec (input : string) (output : list string) : Prop :=
  output = separate_paren_groups_impl input.

(* 测试例子 *)
Example test_separate_paren_groups :
  problem_1_spec
    "(()) (()) "
    ["(())"; "(())"].
Proof.
  unfold problem_1_spec, separate_paren_groups_impl.
  change (remove_spaces "(()) (()) ") with "(())(())".
  simpl.
  vm_compute.
  reflexivity.
Qed.