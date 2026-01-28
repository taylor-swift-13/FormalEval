Require Import ZArith.
Require Import String.
Require Import PArith.
Open Scope Z_scope.
Open Scope string_scope.

(* 定义一个表示输出的类型：可以是二进制字符串或-1 *)
Inductive result : Type :=
  | Binary : string -> result
  | NegativeOne : result.

(*
  一个作用于 positive 类型的递归辅助函数，用于生成二进制字符串。
  这是在 Coq 中进行此类转换的标准方法。
*)
Fixpoint to_binary_p (p : positive) : string :=
  match p with
  | xH    => "1" (* Base case for p = 1 *)
  | xO p' => to_binary_p p' ++ "0" (* Case for p = 2 * p' *)
  | xI p' => to_binary_p p' ++ "1" (* Case for p = 2 * p' + 1 *)
  end.

(*
  主转换函数，用于将 Z 类型（整数）转换为带 "0b" 前缀的二进制字符串。
  它处理了 0 的情况，并使用 to_binary_p 处理正数。
*)
Definition to_binary (n : Z) : string :=
  match n with
  | Z0 => "0b0"
  | Zpos p => "0b" ++ to_binary_p p
  | Zneg _ => "Error: Negative numbers not supported" (* 定义负数的行为 *)
  end.

Definition rounded_avg_impl (n m : Z) : result :=
  if Z.gtb n m then
    NegativeOne
  else
    Binary (to_binary ((n + m) / 2)).

(* n 与 m 为正整数 *)
Definition problem_103_pre (n m : Z) : Prop := n > 0 /\ m > 0.

Definition problem_103_spec (n m : Z) (output : result) : Prop :=
  output = rounded_avg_impl n m.

Example test_problem_103 : problem_103_spec 20002 20001 NegativeOne.
Proof.
  unfold problem_103_spec.
  unfold rounded_avg_impl.
  simpl.
  reflexivity.
Qed.