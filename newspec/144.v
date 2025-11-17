(* def simplify(x, n):
Your task is to implement a function that will simplify the expression
x * n. The function returns True if x * n evaluates to a whole number and False
otherwise. Both x and n, are string representation of a fraction, and have the following format,
<numerator>/<denominator> where both numerator and denominator are positive whole numbers.

You can assume that x, and n are valid fractions, and do not have zero as denominator.

simplify("1/5", "5/1") = True
simplify("1/6", "2/1") = False
simplify("7/10", "10/2") = False *)
(* 导入所需的Coq库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

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

Fixpoint find_slash (l : list ascii) : option (list ascii * list ascii) :=
  match l with
  | [] => None
  | "/"%char :: rest => Some ([], rest)
  | h :: t =>
      match find_slash t with
      | None => None
      | Some (num_s, den_s) => Some (h :: num_s, den_s)
      end
  end.

Definition parse_fraction_impl (s : list ascii) : option (nat * nat) :=
  match find_slash s with
  | None => None
  | Some (num_s, den_s) =>
      Some (list_ascii_to_nat (rev num_s), list_ascii_to_nat den_s)
  end.

Definition simplify_impl (x n : list ascii) : bool :=
  match parse_fraction_impl x, parse_fraction_impl n with
  | Some (num_x, den_x), Some (num_n, den_n) =>
      let product_num := num_x * num_n in
      let product_den := den_x * den_n in
      if (product_num mod product_den) =? 0
      then true
      else false
  | _, _ => false
  end.

(* 约束：x 与 n 均为有效分数串，且分子/分母为正整数 *)
Definition Pre (x n : list ascii) : Prop :=
  exists nx dx ny dy,
    parse_fraction_impl x = Some (nx, dx) /\
    parse_fraction_impl n = Some (ny, dy) /\
    nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0.

Definition simplify_spec (x n : list ascii) (output : bool) : Prop :=
  output = simplify_impl x n.