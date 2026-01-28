Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

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
    let len_nat := Z.to_nat (e_inter - s_inter) in
    (* 规约：
       - 如果交集长度是素数，那么输出必须是 "YES"。
       - 如果交集长度不是素数，那么输出必须是 "NO"。
       我们用逻辑 "或" (\/) 来连接这两种可能。*)
    (prime (Z.of_nat len_nat) /\ output = "YES") \/
    (~prime (Z.of_nat len_nat) /\ output = "NO")
  else
    (* 情况2: 区间不相交，输出必须是 "NO" *)
    output = "NO".

Example test_intersection_1_5_and_1_5 : problem_127_spec (1, 5) (1, 5) "NO".
Proof.
  unfold problem_127_spec.
  simpl.
  right.
  split.
  - intro H.
    (* H : prime 4 *)
    (* We prove that 4 is not prime by finding a divisor (2) *)
    destruct H as [_ Hrel].
    (* Hrel : forall n : Z, 1 <= n < 4 -> rel_prime n 4 *)
    specialize (Hrel 2).
    assert (H_range : 1 <= 2 < 4) by lia.
    apply Hrel in H_range.
    unfold rel_prime in H_range.
    (* H_range : Z.gcd 2 4 = 1 *)
    compute in H_range.
    (* H_range reduces to 2 = 1, which is a contradiction *)
    discriminate.
  - reflexivity.
Qed.