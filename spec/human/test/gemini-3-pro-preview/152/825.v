Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

(* 输入两个列表长度必须相等 *)
Definition problem_152_pre (game guess : list Z) : Prop := length game = length guess.

(*
  compare_spec 定义了 'compare' 函数的规约。
*)
Definition problem_152_spec (game guess result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  forall i, (i < length game)%nat ->
    nth i result 0%Z = Z.abs (nth i game 0%Z - nth i guess 0%Z).

Example test_problem_152:
  problem_152_spec
    [60; 72; 61; 48]
    [60; 72; 61; 48]
    [0; 0; 0; 0].
Proof.
  unfold problem_152_spec.
  split.
  - simpl. reflexivity.
  - split.
    + simpl. reflexivity.
    + intros i Hi.
      do 4 (destruct i; [ simpl; reflexivity | ]).
      simpl in Hi.
      lia.
Qed.