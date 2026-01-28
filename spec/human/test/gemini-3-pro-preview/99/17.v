(* 引入 Coq 的整数库 ZArith 和实数库 Reals *)
Require Import ZArith Reals Lra.
(* 开放 Z 和 R 的作用域，以方便地使用它们的运算符 *)
Open Scope Z_scope.
Open Scope R_scope.

(* 任意实数输入均合法 *)
Definition problem_99_pre (r : R) : Prop := True.

(*
  程序规约 `closest_integer_spec` (已修正类型)

  它是一个二元谓词，描述了输入实数 `r` 和输出整数 `res` 之间必须满足的关系。
 *)
Definition problem_99_spec (r : R) (res : Z) : Prop :=
  (*
    条件1：`res` 是离 `r` 最近的整数之一。
    (此部分无需修改)
   *)
  (forall z : Z, Rabs (r - IZR res) <= Rabs (r - IZR z))
  /\
  (*
    条件2：处理距离相等的情况（平局）。
    如果存在另一个不等于 `res` 的整数 `z`，它与 `r` 的距离相等，
    那么 `res` 的绝对值必须大于或等于 `z` 的绝对值。
   *)
  (forall z : Z, Rabs (r - IZR res) = Rabs (r - IZR z) /\ res <> z -> Rabs (IZR res) >= Rabs (IZR z)).

Example test_case : problem_99_spec 0 0.
Proof.
  unfold problem_99_spec.
  split.
  - (* Prove that 0 is closest to 0 *)
    intros z.
    replace (0 - IZR 0) with 0 by (simpl; lra).
    rewrite Rabs_R0.
    apply Rabs_pos.
  - (* Prove tie-breaking condition *)
    intros z [H_dist H_neq].
    replace (0 - IZR 0) with 0 in H_dist by (simpl; lra).
    rewrite Rabs_R0 in H_dist.
    symmetry in H_dist.
    (* If |0 - z| = 0, then z must be 0 *)
    assert (H_eq : IZR 0 = IZR z).
    {
      destruct (Rcase_abs (0 - IZR z)) as [Hlt | Hge].
      * rewrite (Rabs_left _ Hlt) in H_dist. lra.
      * rewrite (Rabs_right _ Hge) in H_dist. lra.
    }
    apply eq_IZR in H_eq.
    contradiction.
Qed.