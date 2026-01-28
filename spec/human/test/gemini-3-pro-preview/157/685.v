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

(* Test case: input = [11; 13; 14], output = false *)
Example test_problem_157 : problem_157_spec 11 13 14 false.
Proof.
  (* Unfold the specification definition *)
  unfold problem_157_spec.
  
  (* The goal is an equivalence (false = true <-> ...), so we split it *)
  split.
  
  - (* Left to Right: false = true -> ... *)
    intro H.
    (* false = true is a contradiction *)
    discriminate.
    
  - (* Right to Left: (equations) -> false = true *)
    intro H.
    (* The hypothesis H states that one of the Pythagorean equations holds for 11, 13, 14.
       However:
       11^2 + 13^2 = 121 + 169 = 290 <> 14^2 (196)
       11^2 + 14^2 = 121 + 196 = 317 <> 13^2 (169)
       13^2 + 14^2 = 169 + 196 = 365 <> 11^2 (121)
       Lia can solve this arithmetic contradiction. *)
    lia.
Qed.