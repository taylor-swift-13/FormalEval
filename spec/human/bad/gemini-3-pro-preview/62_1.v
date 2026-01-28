Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope Z_scope.

Definition problem_62_pre (xs : list Z) : Prop := True.

Definition problem_62_spec (xs ys : list Z) : Prop :=
  length ys = Nat.sub (length xs) 1 /\
  forall (i : nat),
    (i < length ys)%nat ->
    nth i ys 0 = (Z.of_nat (i + 1)) * (nth (i + 1) xs 0).

Example test_case_62 : problem_62_spec [3; 1; 2; 4; 5] [1; 4; 12; 20].
Proof.
  unfold problem_62_spec.
  split.
  - (* Verify length condition *)
    simpl. reflexivity.
  - (* Verify element-wise condition *)
    intros i Hi.
    (* We destruct i to check each valid index 0, 1, 2, 3.
       For i >= 4, the hypothesis Hi (i < 4) becomes false. *)
    destruct i.
    + (* i = 0 *)
      simpl. reflexivity.
    + destruct i.
      * (* i = 1 *)
        simpl. reflexivity.
      * destruct i.
        -- (* i = 2 *)
           simpl. reflexivity.
        -- destruct i.
           ++ (* i = 3 *)
              simpl. reflexivity.
           ++ (* i >= 4 *)
              simpl in Hi.
              (* Hi simplifies to (n < 0) which is impossible *)
              apply Nat.nlt_0_r in Hi.
              contradiction.
Qed.