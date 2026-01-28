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

Example test_case : problem_99_spec 5.5 6.
Proof.
  unfold problem_99_spec.
  split.
  - (* Prove that 6 is closest to 5.5 *)
    intros z.
    (* |5.5 - 6| = |-0.5| = 0.5 *)
    replace (5.5 - IZR 6) with (-0.5) by (simpl; lra).
    rewrite Rabs_Ropp.
    replace (Rabs 0.5) with 0.5 by (simpl; lra).
    
    (* Split cases for z: z <= 5 or z >= 6 (since z > 5 implies z >= 6 for integers) *)
    destruct (Z_le_gt_dec z 5).
    + (* Case z <= 5 *)
      assert (H_le: IZR z <= 5). { apply IZR_le; assumption. }
      (* |5.5 - z| = 5.5 - z. We need to show 0.5 <= 5.5 - z, which is z <= 5 *)
      destruct (Rcase_abs (5.5 - IZR z)) as [Hlt | Hge].
      * (* 5.5 - z < 0 -> z > 5.5, contradicts z <= 5 *)
        lra.
      * (* 5.5 - z >= 0 *)
        rewrite (Rabs_right _ Hge). lra.
    + (* Case z > 5 *)
      assert (H_ge: (6 <= z)%Z). { apply Z.le_succ_l. apply Z.gt_lt. assumption. }
      apply IZR_le in H_ge. (* implies 6 <= IZR z *)
      (* |5.5 - z| = z - 5.5. We need to show 0.5 <= z - 5.5, which is z >= 6 *)
      destruct (Rcase_abs (5.5 - IZR z)) as [Hlt | Hge].
      * (* 5.5 - z < 0 *)
        rewrite (Rabs_left _ Hlt). lra.
      * (* 5.5 - z >= 0 -> z <= 5.5, contradicts z >= 6 *)
        lra.
  - (* Prove tie-breaking condition *)
    intros z [H_dist H_neq].
    replace (5.5 - IZR 6) with (-0.5) in H_dist by (simpl; lra).
    rewrite Rabs_Ropp in H_dist.
    replace (Rabs 0.5) with 0.5 in H_dist by (simpl; lra).
    
    destruct (Rcase_abs (5.5 - IZR z)) as [Hlt | Hge].
    + (* 5.5 - z < 0 -> -(5.5 - z) = 0.5 -> z = 6 *)
      rewrite (Rabs_left _ Hlt) in H_dist.
      assert (Heq: IZR z = 6) by lra.
      apply eq_IZR in Heq.
      contradiction. (* z cannot be 6 due to H_neq *)
    + (* 5.5 - z >= 0 -> 5.5 - z = 0.5 -> z = 5 *)
      rewrite (Rabs_right _ Hge) in H_dist.
      assert (Heq: IZR z = 5) by lra.
      apply eq_IZR in Heq.
      subst.
      (* Need to show |6| >= |5| *)
      replace (Rabs (IZR 6)) with 6 by (simpl; lra).
      replace (Rabs (IZR 5)) with 5 by (simpl; lra).
      lra.
Qed.