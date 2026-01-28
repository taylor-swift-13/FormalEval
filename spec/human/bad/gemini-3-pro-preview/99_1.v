Require Import ZArith Reals Psatz.
Open Scope Z_scope.
Open Scope R_scope.

(* 任意实数输入均合法 *)
Definition Pre (r : R) : Prop := True.

(*
  程序规约 `closest_integer_spec`
 *)
Definition closest_integer_spec (r : R) (res : Z) : Prop :=
  (*
    条件1：`res` 是离 `r` 最近的整数之一。
   *)
  (forall z : Z, Rabs (r - IZR res) <= Rabs (r - IZR z))
  /\
  (*
    条件2：处理距离相等的情况（平局）。
    如果存在另一个不等于 `res` 的整数 `z`，它与 `r` 的距离相等，
    那么 `res` 的绝对值必须大于或等于 `z` 的绝对值。
   *)
  (forall z : Z, Rabs (r - IZR res) = Rabs (r - IZR z) /\ res <> z -> Rabs (IZR res) >= Rabs (IZR z)).

(* Test case: input = ["10"], output = 10%Z *)
Example test_case_1 : closest_integer_spec 10 10.
Proof.
  unfold closest_integer_spec.
  split.
  - (* Condition 1: Minimality *)
    intros z.
    (* Simplify (10 - 10) to 0 *)
    replace (10 - IZR 10) with 0 by lra.
    rewrite Rabs_R0.
    (* |0| <= |x| is always true because absolute value is non-negative *)
    apply Rabs_pos.
  - (* Condition 2: Tie-breaking *)
    intros z [Hdist Hneq].
    (* Simplify (10 - 10) to 0 *)
    replace (10 - IZR 10) with 0 in Hdist by lra.
    rewrite Rabs_R0 in Hdist.
    symmetry in Hdist.
    (* We have Rabs (10 - IZR z) = 0. We need to prove z = 10 to contradict Hneq. *)
    (* Case analysis on the sign of (10 - IZR z) to unfold Rabs *)
    destruct (Rcase_abs (10 - IZR z)) as [Hlt | Hge].
    + (* Case: 10 - IZR z < 0 *)
      rewrite (Rabs_left _ Hlt) in Hdist.
      assert (Heq: IZR z = 10) by lra.
      apply eq_IZR in Heq.
      contradiction.
    + (* Case: 10 - IZR z >= 0 *)
      rewrite (Rabs_right _ Hge) in Hdist.
      assert (Heq: IZR z = 10) by lra.
      apply eq_IZR in Heq.
      contradiction.
Qed.