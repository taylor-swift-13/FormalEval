Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

Import ListNotations.

(*
  辅助函数，用于将一个数字字符（如 '0', '1', ...）
  转换为其对应的自然数（如 0, 1, ...）。
*)
Definition nat_of_digit (c : ascii) : nat :=
  Ascii.nat_of_ascii c - Ascii.nat_of_ascii "0"%char.

(*
  程序规约 Spec 的定义。
  - x:      输入的非负整数。
  - base:   转换的目标基数 (>= 2)。
  - output: 转换后得到的字符串。
*)
(* Pre: base must be at least 2 for a valid base conversion *)
Definition problem_44_pre (x : nat) (base : nat) : Prop := (base >= 2)%nat /\ (base < 10)%nat.

Definition problem_44_spec (x : nat) (base : nat) (output : list ascii) : Prop :=
  (* 将字符列表转换为一个由数字组成的列表 *)
  let digits := List.map nat_of_digit output in

  (*
    规约的第一个条件：
    输出字符串中的每一个数字都必须小于基数 base。
   *)
  (Forall (fun d => d < base) digits) /\

  (*
    规约的第二个条件（使用霍纳法则）：
    字符串所代表的数值，按 base 展开后应等于 x。
    对于列表 [d_0, d_1, ..., d_k]，该表达式计算：
    (...((0 * base + d_0) * base + d_1) * ... + d_k)
    这等价于 ∑ (d_i * base^(k-i))。
   *)
  (fold_left (fun acc d => acc * base + d) digits 0 = x).

Example test_case_245678_3 : problem_44_spec 245678 3 ["1"%char; "1"%char; "0"%char; "1"%char; "1"%char; "1"%char; "0"%char; "0"%char; "0"%char; "0"%char; "1"%char; "2"%char].
Proof.
  unfold problem_44_spec.
  split.
  - vm_compute.
    repeat constructor.
  - vm_compute.
    reflexivity.
Qed.