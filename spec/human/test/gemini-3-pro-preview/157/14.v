Require Import ZArith.
Require Import Psatz. (* For lia tactic *)
Open Scope Z_scope.

(* 任意整数边长输入 *)
Definition problem_157_pre (a b c : Z) : Prop :=   (a > 0 /\ b > 0 /\ c > 0).

(*
  right_angle_triangle_spec a b c res

  - a, b, c: 代表三角形三边长度的整数 (Z)。
  - res: 程序的布尔值输出 (bool)。

  该规约规定，如果输入 a, b, c 均为正数，
  那么当且仅当这三条边满足勾股定理的任意一种排列时，
  程序的返回结果 res 为 true。
*)
Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

(* Test case: input = [7; 9; 12], output = false *)
Example test_problem_157 : problem_157_spec 7 9 12 false.
Proof.
  unfold problem_157_spec.
  split.
  - intro H.
    discriminate H.
  - intro H.
    (* The hypothesis H states that one of the Pythagorean equations holds.
       We can check the arithmetic:
       7*7 + 9*9 = 49 + 81 = 130 <> 144 (12*12)
       7*7 + 12*12 = 49 + 144 = 193 <> 81 (9*9)
       9*9 + 12*12 = 81 + 144 = 225 <> 49 (7*7)
       Lia can solve these contradictions automatically. *)
    lia.
Qed.