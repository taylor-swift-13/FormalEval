(* 引入 Coq 中关于列表和整数的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

(* 定义问题规范 *)
Definition problem_62_pre (xs : list Z) : Prop := True.

Definition problem_62_spec (xs ys : list Z) : Prop :=
  length ys = Nat.sub (length xs) 1 /\
  forall (i : nat),
    (i < length ys)%nat ->
    nth i ys 0 = (Z.of_nat (i + 1)) * (nth (i + 1) xs 0).

(* 定义导数函数 *)
Definition derivative (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | _ :: xs' =>
      List.map (fun '(i, coef) => Z.of_nat (i + 1) * coef)
               (List.combine (List.seq 1 (length xs')) xs')
  end.

(* 证明导数函数满足规范 *)
Lemma derivative_correct : forall xs,
  problem_62_spec xs (derivative xs).
Proof.
  intros xs. unfold problem_62_spec.
  destruct xs as [| a xs'].
  - simpl. split; reflexivity.
  - simpl. split.
    + rewrite map_length, combine_length, seq_length, Nat.min_id; reflexivity.
    + intros i Hi. rewrite map_nth.
      rewrite nth_combine; try (rewrite seq_length; lia).
      rewrite seq_nth; try lia.
      simpl. reflexivity.
Qed.

Example test_derivative : derivative [3; 1; 2; 4; 5] = [1; 4; 12; 20].
Proof.
  simpl. reflexivity.
Qed.