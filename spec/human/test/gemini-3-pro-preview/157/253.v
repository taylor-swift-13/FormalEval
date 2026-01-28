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

(* Test case: input = [37; 226; 37], output = false *)
Example test_problem_157 : problem_157_spec 37 226 37 false.
Proof.
  (* Unfold the specification definition *)
  unfold problem_157_spec.
  
  (* The goal is an equivalence (false = true <-> ...), so we split it *)
  split.
  
  - (* Left to Right: false = true -> (equations) *)
    intro H.
    (* false = true is a contradiction *)
    inversion H.
    
  - (* Right to Left: (equations) -> false = true *)
    intro H.
    (* We examine the three cases of the disjunction *)
    destruct H as [H1 | [H2 | H3]].
    + (* Case 1: 37^2 + 226^2 = 37^2 *)
      (* This implies 226^2 = 0, which is false *)
      lia.
    + (* Case 2: 37^2 + 37^2 = 226^2 *)
      (* 1369 + 1369 = 2738, which is not equal to 226^2 (51076) *)
      lia.
    + (* Case 3: 226^2 + 37^2 = 37^2 *)
      (* This implies 226^2 = 0, which is false *)
      lia.
Qed.