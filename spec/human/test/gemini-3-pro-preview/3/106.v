Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1; 1; 1; 1; 4; 4] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Heq Hlt]]].
    destruct prefix as [|x1 p1].
    + simpl in Hlt. lia.
    + simpl in Heq. injection Heq as Hx1 Heq1. subst x1.
      destruct p1 as [|x2 p2].
      * simpl in Hlt. lia.
      * simpl in Heq1. injection Heq1 as Hx2 Heq2. subst x2.
        destruct p2 as [|x3 p3].
        -- simpl in Hlt. lia.
        -- simpl in Heq2. injection Heq2 as Hx3 Heq3. subst x3.
           destruct p3 as [|x4 p4].
           ++ simpl in Hlt. lia.
           ++ simpl in Heq3. injection Heq3 as Hx4 Heq4. subst x4.
              destruct p4 as [|x5 p5].
              ** simpl in Hlt. lia.
              ** simpl in Heq4. injection Heq4 as Hx5 Heq5. subst x5.
                 destruct p5 as [|x6 p6].
                 --- simpl in Hlt. lia.
                 --- simpl in Heq5. injection Heq5 as Hx6 Heq6. subst x6.
                     destruct p6 as [|x7 p7].
                     +++ simpl in Hlt. lia.
                     +++ simpl in Heq6. discriminate.
  - intros H. discriminate H.
Qed.