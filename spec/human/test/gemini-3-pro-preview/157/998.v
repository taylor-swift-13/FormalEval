Require Import Reals.
Require Import Psatz. (* For nra tactic *)
Open Scope R_scope.

(* 任意实数边长输入 *)
Definition problem_157_pre (a b c : R) : Prop :=   (a > 0 /\ b > 0 /\ c > 0).

(*
  right_angle_triangle_spec a b c res

  - a, b, c: 代表三角形三边长度的实数 (R)。
  - res: 程序的布尔值输出 (bool)。

  该规约规定，如果输入 a, b, c 均为正数，
  那么当且仅当这三条边满足勾股定理的任意一种排列时，
  程序的返回结果 res 为 true。
*)
Definition problem_157_spec (a b c : R) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

(* Test case: input = [25.16373529161418; 94.48837938393268; 94.48837938393268], output = false *)
Example test_problem_157 : problem_157_spec 25.16373529161418%R 94.48837938393268%R 94.48837938393268%R false.
Proof.
  (* Unfold the specification definition *)
  unfold problem_157_spec.
  
  (* The goal is an equivalence (false = true <-> ...), so we split it *)
  split.
  
  - (* Left to Right: false = true -> (equations) *)
    intro H.
    (* false = true is a contradiction *)
    discriminate.
    
  - (* Right to Left: (equations) -> false = true *)
    intro H.
    (* The goal is effectively False, derived from the contradiction in H with specific values *)
    destruct H as [H | [H | H]];
    (* nra (Non-linear Real Arithmetic) can verify these equations are impossible for the given constants *)
    nra.
Qed.