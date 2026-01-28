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

(* Test case: input = [12; 21; 20], output = false *)
Example test_problem_157 : problem_157_spec 12 21 20 false.
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
    (* Break down the disjunction of equations *)
    destruct H as [H | [H | H]].
    + (* Case 1: 12^2 + 21^2 = 20^2 *)
      (* 144 + 441 = 400 -> 585 = 400 *)
      vm_compute in H.
      discriminate H.
    + (* Case 2: 12^2 + 20^2 = 21^2 *)
      (* 144 + 400 = 441 -> 544 = 441 *)
      vm_compute in H.
      discriminate H.
    + (* Case 3: 21^2 + 20^2 = 12^2 *)
      (* 441 + 400 = 144 -> 841 = 144 *)
      vm_compute in H.
      discriminate H.
Qed.