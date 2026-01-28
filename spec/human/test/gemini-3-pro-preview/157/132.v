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

(* Test case: input = [13; 14; 16], output = false *)
Example test_problem_157 : problem_157_spec 13 14 16 false.
Proof.
  unfold problem_157_spec.
  split.
  - (* Left to Right: false = true -> ... *)
    intro H.
    inversion H.
  - (* Right to Left: equations -> false = true *)
    intro H.
    (* We need to show that assuming any of the pythagorean equations holds leads to a contradiction,
       since 13, 14, 16 do not form a right triangle. *)
    destruct H as [H1 | [H2 | H3]].
    + (* Case 1: 13^2 + 14^2 = 16^2 -> 169 + 196 = 256 -> 365 = 256 *)
      simpl in H1.
      discriminate H1.
    + (* Case 2: 13^2 + 16^2 = 14^2 -> 169 + 256 = 196 -> 425 = 196 *)
      simpl in H2.
      discriminate H2.
    + (* Case 3: 14^2 + 16^2 = 13^2 -> 196 + 256 = 169 -> 452 = 169 *)
      simpl in H3.
      discriminate H3.
Qed.