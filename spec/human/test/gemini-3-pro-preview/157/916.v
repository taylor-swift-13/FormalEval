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

(* Test case: input = [9; 13; 15], output = false *)
Example test_problem_157 : problem_157_spec 9 13 15 false.
Proof.
  unfold problem_157_spec.
  split.
  - intro H.
    (* false = true is a contradiction *)
    discriminate H.
  - intro H.
    (* The hypothesis H says 9, 13, 15 form a right triangle, which is arithmetically false.
       9^2 + 13^2 = 81 + 169 = 250 != 225 (15^2)
       9^2 + 15^2 = 81 + 225 = 306 != 169 (13^2)
       13^2 + 15^2 = 169 + 225 = 394 != 81 (9^2)
       lia solves this contradiction. *)
    lia.
Qed.