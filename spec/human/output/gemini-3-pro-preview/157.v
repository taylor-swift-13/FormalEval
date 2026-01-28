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

(* Test case: input = [3; 4; 5], output = true *)
Example test_problem_157 : problem_157_spec 3 4 5 true.
Proof.
  (* Unfold the specification definition *)
  unfold problem_157_spec.
  
  (* The goal is an equivalence (true = true <-> ...), so we split it *)
  split.
  
  - (* Left to Right: true = true -> (equations) *)
    intro H.
    (* We know 3^2 + 4^2 = 5^2 (9 + 16 = 25), so we choose the first case *)
    left.
    (* Simplify the arithmetic expressions *)
    simpl.
    (* 25 = 25 holds *)
    reflexivity.
    
  - (* Right to Left: (equations) -> true = true *)
    intro H.
    (* true = true is trivially true *)
    reflexivity.
Qed.