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

Example test_intersection_1_2_and_2_3 : problem_127_spec (1, 2) (2, 3) "NO".
Proof.
  (* Unfold the specification to expose the logic *)
  unfold problem_127_spec.
  
  (* Simplify the arithmetic expressions.
     s_inter = Z.max 1 2 = 2
     e_inter = Z.min 2 3 = 2
     Z.leb 2 2 = true
     len_nat = Z.to_nat (2 - 2) = 0 *)
  simpl.
  
  (* The goal is now: (prime 0 /\ "NO" = "YES") \/ (~ prime 0 /\ "NO" = "NO") *)
  (* We need to prove the right side since the expected output is "NO" and 0 is not prime. *)
  right.
  
  (* Split into two subgoals: ~prime 0 and "NO" = "NO" *)
  split.
  - (* Subgoal 1: Prove 0 is not prime *)
    intro H.
    (* prime is an inductive type, so we use inversion to inspect the constructor *)
    inversion H.
    (* The definition of prime p requires 1 < p. Here p=0, so 1 < 0, which is false. *)
    lia.
  - (* Subgoal 2: Prove "NO" = "NO" *)
    reflexivity.
Qed.