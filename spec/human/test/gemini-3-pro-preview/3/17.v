Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [15; 2; 3; -6] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [H1 H2]]].
    destruct prefix as [|x1 t1].
    + simpl in H2. lia.
    + simpl in H1. injection H1 as Ex1 Et1. subst x1.
      destruct t1 as [|x2 t2].
      * simpl in H2. lia.
      * simpl in Et1. injection Et1 as Ex2 Et2. subst x2.
        destruct t2 as [|x3 t3].
        -- simpl in H2. lia.
        -- simpl in Et2. injection Et2 as Ex3 Et3. subst x3.
           destruct t3 as [|x4 t4].
           ++ simpl in H2. lia.
           ++ simpl in Et3. injection Et3 as Ex4 Et4. subst x4.
              destruct t4 as [|x5 t5].
              ** simpl in H2. lia.
              ** simpl in Et4. discriminate.
  - intros H. discriminate H.
Qed.