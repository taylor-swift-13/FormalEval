Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

(* 辅助函数：将一个数字字符转换为 nat *)
Definition nat_of_digit (c : ascii) : option nat :=
  match c with
  | "0"%char => Some 0
  | "1"%char => Some 1
  | "2"%char => Some 2
  | "3"%char => Some 3
  | "4"%char => Some 4
  | "5"%char => Some 5
  | "6"%char => Some 6
  | "7"%char => Some 7
  | "8"%char => Some 8
  | "9"%char => Some 9
  | _ => None
  end.

(* 辅助函数：将两个字符转换为 nat *)
Definition nat_of_2_digits (c1 c2 : ascii) : option nat :=
  match (nat_of_digit c1, nat_of_digit c2) with
  | (Some d1, Some d2) => Some (10 * d1 + d2)
  | _ => None
  end.

(* 辅助函数：将四个字符转换为 nat *)
Definition nat_of_4_digits (c1 c2 c3 c4 : ascii) : option nat :=
  match (nat_of_digit c1, nat_of_digit c2, nat_of_digit c3, nat_of_digit c4) with
  | (Some d1, Some d2, Some d3, Some d4) => Some (1000 * d1 + 100 * d2 + 10 * d3 + d4)
  | _ => None
  end.

(* 辅助函数：根据月份返回该月的最大天数 *)
Definition days_in_month (m : nat) : nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => 29 (* 根据规则 #2 *)
  | _ => 0 (* 无效月份 *)
  end.

(* 作为校验函数，输入可为任意字符列表 *)
Definition problem_124_pre (s : list ascii) : Prop := True.

(*
  程序规约 (Specification)
  这个 Prop 定义了输入的字符列表 s 若满足所有有效日期规则，则为 True。
*)
Definition problem_124_spec (s : string) : Prop :=
  match list_ascii_of_string s with
  (* 模式匹配 "mm-dd-yyyy" 格式。这隐式地检查了列表长度为10 *)
  | [m1; m2; sep1; d1; d2; sep2; y1; y2; y3; y4] =>
      (* 1. 检查分隔符是否为 '-' *)
      sep1 = "-"%char /\ sep2 = "-"%char /\
      (* 尝试将字符解析为月、日、年 *)
      (exists m d y,
        nat_of_2_digits m1 m2 = Some m /\
        nat_of_2_digits d1 d2 = Some d /\
        nat_of_4_digits y1 y2 y3 y4 = Some y /\
        (* 2. 检查月份范围 (1-12) *)
        (1 <= m <= 12 /\
        (* 3. 检查天数范围 (1 到该月最大天数) *)
         1 <= d <= days_in_month m))
  (* 如果字符列表不符合 10 个字符的格式，则直接判定为无效 *)
  | _ => False
  end.

Example test_valid_date_1 : problem_124_spec "03-11-2000".
Proof.
  unfold problem_124_spec.
  simpl.
  split. { reflexivity. }
  split. { reflexivity. }
  exists 3, 11, 2000.
  repeat split; try reflexivity.
  - lia.
  - lia.
  - simpl. lia.
Qed.