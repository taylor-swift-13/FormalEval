Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
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

Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    num = list_ascii_to_nat num_s /\
    den = list_ascii_to_nat den_s.

Definition problem_144_pre (x n : string) : Prop :=
  exists nx dx ny dy,
    Parse_Fraction (list_ascii_of_string x) nx dx /\
    Parse_Fraction (list_ascii_of_string n) ny dy /\
    nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0.

Definition problem_144_spec (x n : string) (output : bool) : Prop :=
  exists num_x den_x num_n den_n : nat,
    Parse_Fraction (list_ascii_of_string x) num_x den_x /\
    Parse_Fraction (list_ascii_of_string n) num_n den_n /\
    num_x > 0 /\ den_x > 0 /\
    num_n > 0 /\ den_n > 0 /\
    let product_num := num_x * num_n in
    let product_den := den_x * den_n in
    output = if (product_num mod product_den) =? 0
             then true
             else false.

Example problem_144_test1 : problem_144_spec "1/5" "5/1" true.
Proof.
  unfold problem_144_spec.
  exists 1, 5, 5, 1.
  split.
  - (* Parse_Fraction for "1/5" *)
    unfold Parse_Fraction.
    exists ["1"%char], ["5"%char].
    split.
    + simpl. reflexivity.
    + split; reflexivity.
  - split.
    + (* Parse_Fraction for "5/1" *)
      unfold Parse_Fraction.
      exists ["5"%char], ["1"%char].
      split.
      * simpl. reflexivity.
      * split; reflexivity.
    + split; [auto | split; [auto | split; [auto | split; [auto | reflexivity]]]].
Qed.