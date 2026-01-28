Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

(* Adding the Lia library for linear integer arithmetic *)
Require Import Lia.

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

Example test_case_1 : forall number need remaining result,
  problem_159_pre number need remaining ->
  problem_159_spec number need remaining result ->
  number = 5%Z -> need = 6%Z -> remaining = 10%Z ->
  result = [11%Z; 4%Z].
Proof.
  intros number need remaining result Hpre Hspec Hnumber Hneed Hremaining.
  unfold problem_159_pre in Hpre.
  unfold problem_159_spec in Hspec.
  subst number need remaining.
  simpl in *.
  destruct Hspec as [[Hge Hresult] | [Hlt Hresult]].
  - rewrite Hresult. reflexivity.
  - lia. (* This case is impossible as 10 is not less than 6 *)
Qed.