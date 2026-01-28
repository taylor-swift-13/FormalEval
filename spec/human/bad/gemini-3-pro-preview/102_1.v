(* 导入 Coq 的整数库 ZArith *)
Require Import Coq.ZArith.ZArith.
(* 导入 Lia 策略用于处理线性整数算术 *)
Require Import Coq.micromega.Lia.

(* 打开 Z 的作用域，这样就可以直接使用像 +, -, <= 等符号，而不用写 Z.add, Z.sub, Z.le *)
Open Scope Z_scope.

(* x 与 y 均为正整数 *)
Definition problem_102_pre (x y : Z) : Prop := x > 0 /\ y > 0.

(* 
   定义 choose_num 函数的规约 (Specification)
   它描述了输入 x, y 和输出 res 之间必须满足的关系。
*)
Definition problem_102_spec (x y res : Z) : Prop :=

  (* 情况一：当区间 [x, y] 中存在偶数时 *)
  ( (exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (* 那么，输出 res 必须是这个区间内最大的偶数 *)
    (Z.even res = true /\ x <= res /\ res <= y /\ (forall z' : Z, res < z' /\ z' <= y ->  Z.even z' = false)) )
  /\
  (* 情况二：当区间 [x, y] 中不存在偶数时 *)
  ( (~ exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (* 那么，输出 res 必须等于 -1 *)
    res = -1 ).

Example test_case_102 : problem_102_spec 12 15 14.
Proof.
  (* 展开规约定义 *)
  unfold problem_102_spec.
  split.
  
  - (* 证明第一部分：如果存在偶数，则 14 满足最大偶数的条件 *)
    intros H_exists.
    (* 手动分解合取式，确保 tactic 应用在正确的子目标上，避免之前的 unification 错误 *)
    split.
    + (* 证明 14 是偶数: Z.even 14 = true *)
      reflexivity.
    + split.
      * (* 证明 12 <= 14 *)
        lia.
      * split.
        -- (* 证明 14 <= 15 *)
           lia.
        -- (* 证明 14 是范围内最大的偶数 *)
           intros z' H_range.
           (* H_range: 14 < z' /\ z' <= 15 *)
           (* 在整数范围内，14 < z' <= 15 意味着 z' 必须等于 15 *)
           assert (z' = 15) by lia.
           subst.
           (* 证明 15 不是偶数: Z.even 15 = false *)
           reflexivity.

  - (* 证明第二部分：如果不存在偶数，则结果为 -1 (反证法) *)
    intros H_not_exists.
    exfalso. (* 这是一个矛盾的情况，因为显然存在偶数 *)
    apply H_not_exists.
    (* 我们举例证明 14 就是那个存在的偶数 *)
    exists 14.
    split.
    + lia. (* 12 <= 14 <= 15 *)
    + reflexivity. (* 14 是偶数 *)
Qed.