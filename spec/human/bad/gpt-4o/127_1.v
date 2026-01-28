(* 引入所需的基础 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Arith.PeanoNat.

(* 允许使用列表和作用域的标准表示法 *)
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.
Open Scope string_scope.

(* 区间为闭区间，且满足 start <= end *)
Definition problem_127_pre (i1 i2 : Z * Z) : Prop :=
  let '(s1,e1) := i1 in
  let '(s2,e2) := i2 in s1 <= e1 /\ s2 <= e2.

Definition problem_127_spec (i1 i2 : Z * Z) (output : string) : Prop :=
  let (s1, e1) := i1 in
  let (s2, e2) := i2 in

  (* 计算交集的起始点和结束点 *)
  let s_inter := Z.max s1 s2 in
  let e_inter := Z.min e1 e2 in

  (* 分情况讨论：区间是否相交 *)
  if Z.leb s_inter e_inter then
    (* 情况1: 区间相交 *)
    let len_nat := Z.to_nat (e_inter - s_inter + 1) in
    (* 规约：
       - 如果交集长度是素数，那么输出必须是 "YES"。
       - 如果交集长度不是素数，那么输出必须是 "NO"。
       我们用逻辑 "或" (\/) 来连接这两种可能。*)
    (prime (Z.of_nat len_nat) /\ output = "YES") \/
    (~prime (Z.of_nat len_nat) /\ output = "NO")
  else
    (* 情况2: 区间不相交，输出必须是 "NO" *)
    output = "NO".

Example problem_127_test_case_1 :
  problem_127_spec (1, 2) (2, 3) "NO".
Proof.
  unfold problem_127_spec.
  simpl.
  (* 计算交集的起始点和结束点 *)
  remember (Z.max 1 2) as s_inter.
  remember (Z.min 2 3) as e_inter.
  (* 检查区间是否相交 *)
  assert (Z.leb s_inter e_inter = true).
  { subst; simpl; lia. }
  rewrite H.
  simpl.
  (* 计算交集长度 *)
  remember (Z.to_nat (e_inter - s_inter + 1)) as len_nat.
  assert (len_nat = 1) by (subst; simpl; lia).
  subst len_nat.
  simpl.
  (* 检查素数性 *)
  right.
  split.
  - unfold prime.
    intros [p [Hp1 Hp2]].
    destruct Hp1; simpl; lia.
  - reflexivity.
Qed.