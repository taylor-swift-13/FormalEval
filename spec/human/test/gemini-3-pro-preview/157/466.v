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

(* Test case: input = [2021; 49; 13], output = false *)
Example test_problem_157 : problem_157_spec 2021 49 13 false.
Proof.
  (* Unfold the specification definition *)
  unfold problem_157_spec.
  
  (* The goal is an equivalence (false = true <-> ...), so we split it *)
  split.
  
  - (* Left to Right: false = true -> ... *)
    intro H.
    (* false = true is a contradiction *)
    inversion H.
    
  - (* Right to Left: (equations) -> false = true *)
    intro H.
    (* We have a disjunction of equations, all of which are false for these values *)
    destruct H as [H1 | [H2 | H3]].
    + (* Case 1: 2021^2 + 49^2 = 13^2 *)
      simpl in H1.
      (* 4086842 = 169 is false *)
      discriminate H1.
    + (* Case 2: 2021^2 + 13^2 = 49^2 *)
      simpl in H2.
      (* 4084610 = 2401 is false *)
      discriminate H2.
    + (* Case 3: 49^2 + 13^2 = 2021^2 *)
      simpl in H3.
      (* 2570 = 4084441 is false *)
      discriminate H3.
Qed.