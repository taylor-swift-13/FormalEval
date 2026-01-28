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

(* Test case: input = [12; 16; 15], output = false *)
Example test_problem_157 : problem_157_spec 12 16 15 false.
Proof.
  (* Unfold the specification definition *)
  unfold problem_157_spec.
  
  (* The goal is an equivalence (false = true <-> ...), so we split it *)
  split.
  
  - (* Left to Right: false = true -> ... *)
    intro H.
    (* false = true is a contradiction *)
    discriminate H.
    
  - (* Right to Left: (equations) -> false = true *)
    intro H.
    (* The equations lead to a contradiction with integer arithmetic *)
    (* 12^2 + 16^2 = 144 + 256 = 400 <> 15^2 (225) *)
    (* 12^2 + 15^2 = 144 + 225 = 369 <> 16^2 (256) *)
    (* 16^2 + 15^2 = 256 + 225 = 481 <> 12^2 (144) *)
    lia.
Qed.