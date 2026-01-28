Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_62_pre (xs : list Z) : Prop := True.

Definition problem_62_spec (xs ys : list Z) : Prop :=
  length ys = Nat.sub (length xs) 1 /\
  forall (i : nat),
    (i < length ys)%nat ->
    nth i ys 0 = (Z.of_nat (i + 1)) * (nth (i + 1) xs 0).

Example test_derivative_2 :
  problem_62_spec [2%Z; 0%Z; 3%Z; 0%Z; 1%Z; 0%Z; 0%Z; -2%Z; 0%Z; 6%Z; 0%Z; 0%Z] [0%Z; 6%Z; 0%Z; 4%Z; 0%Z; 0%Z; -14%Z; 0%Z; 54%Z; 0%Z; 0%Z].
Proof.
  unfold problem_62_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    destruct i as [| i']; [simpl; reflexivity |].
    destruct i' as [| i'']; [simpl; reflexivity |].
    destruct i'' as [| i''']; [simpl; reflexivity |].
    destruct i''' as [| i'''']; [simpl; reflexivity |].
    destruct i'''' as [| i''''']; [simpl; reflexivity |].
    destruct i''''' as [| i'''''']; [simpl; reflexivity |].
    destruct i'''''' as [| i''''''']; [simpl; reflexivity |].
    destruct i''''''' as [| i'''''''']; [simpl; reflexivity |].
    destruct i'''''''' as [| i''''''''']; [simpl; reflexivity |].
    destruct i''''''''' as [| i'''''''''']; [simpl; reflexivity |].
    destruct i'''''''''' as [| i''''''''''']; [simpl; reflexivity |].
    simpl in Hi.
    lia.
Qed.