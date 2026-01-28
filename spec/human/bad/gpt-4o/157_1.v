Require Import ZArith.
Open Scope Z_scope.

(* 任意整数边长输入 *)
Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

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

Example problem_157_test : problem_157_spec 3 4 5 true.
Proof.
  unfold problem_157_spec.
  split.
  - intros H.
    right; left.
    simpl.
    reflexivity.
  - intros H.
    destruct H as [H | [H | H]]; simpl in H;
    try (apply Z.eq_square_0 in H; lia).
    reflexivity.
Qed.