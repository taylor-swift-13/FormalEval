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

(* Test case: input = [16; 7; 20], output = false *)
Example test_problem_157 : problem_157_spec 16 7 20 false.
Proof.
  unfold problem_157_spec.
  split.
  - intro H.
    (* Left to Right: false = true -> ... *)
    (* This direction is trivial because the premise is false *)
    discriminate H.
  - intro H.
    (* Right to Left: (equations) -> false = true *)
    (* We need to show that the equations imply a contradiction, 
       since false = true is False. *)
    (* 16^2 + 7^2 = 305 != 20^2 (400) *)
    (* 16^2 + 20^2 = 656 != 7^2 (49) *)
    (* 7^2 + 20^2 = 449 != 16^2 (256) *)
    (* The arithmetic solver 'lia' can verify these inequalities *)
    lia.
Qed.