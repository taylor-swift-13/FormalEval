Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

(* 约束：0 <= number,need,remaining <= 1000 *)
Definition problem_159_pre (number need remaining : Z) : Prop :=
  0 <= number /\ 0 <= need /\ 0 <= remaining /\
  number <= 1000 /\ need <= 1000 /\ remaining <= 1000.

(*
  number: 已吃的胡萝卜数量
  need: 需要吃的胡萝卜数量
  remaining: 库存中剩余的胡萝卜数量
  result: 一个列表，包含两个整数 [最终吃掉的胡萝卜总数, 最终剩余的胡萝卜数量]
*)
Definition problem_159_spec (number need remaining : Z) (result : list Z) : Prop :=
  (Z.ge remaining need /\ result = (number + need) :: (remaining - need) :: nil) \/
  (Z.lt remaining need /\ result = (number + remaining) :: 0 :: nil).

Example test_problem_159_pre : problem_159_pre 504%Z 1000%Z 1000%Z.
Proof.
  unfold problem_159_pre.
  repeat split; lia.
Qed.

Example test_problem_159_spec : problem_159_spec 504%Z 1000%Z 1000%Z [1504%Z; 0%Z].
Proof.
  unfold problem_159_spec.
  left.
  split.
  - lia.
  - now compute.
Qed.