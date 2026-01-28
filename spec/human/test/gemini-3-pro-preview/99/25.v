(* 引入 Coq 的整数库 ZArith 和实数库 Reals *)
Require Import ZArith Reals Lra Lia.
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

Example test_case : problem_99_spec (-999.99) (-1000).
Proof.
  unfold problem_99_spec.
  split.
  - intros z.
    replace (-999.99 - IZR (-1000)) with 0.01 by (simpl; lra).
    rewrite Rabs_right; [|lra].
    destruct (Z.eq_dec z (-1000)) as [Heq | Hneq].
    + subst. replace (-999.99 - IZR (-1000)) with 0.01 by (simpl; lra).
      rewrite Rabs_right; lra.
    + assert (Hrange: (z <= -1001 \/ z >= -999)%Z) by lia.
      destruct Hrange as [Hle | Hge].
      * apply IZR_le in Hle.
        rewrite Rabs_right; lra.
      * apply IZR_ge in Hge.
        rewrite Rabs_left; lra.
  - intros z [Hdist Hneq].
    replace (-999.99 - IZR (-1000)) with 0.01 in Hdist by (simpl; lra).
    rewrite Rabs_right in Hdist; [|lra].
    assert (Hrange: (z <= -1001 \/ z >= -999)%Z) by lia.
    destruct Hrange as [Hle | Hge].
    + apply IZR_le in Hle.
      rewrite Rabs_right in Hdist; lra.
    + apply IZR_ge in Hge.
      rewrite Rabs_left in Hdist; lra.
Qed.