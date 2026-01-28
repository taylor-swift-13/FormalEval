Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_2: problem_3_spec [1%Z; 2%Z; 3%Z; -6%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [H_eq H_lt]]].
    destruct prefix as [|z1 prefix].
    + simpl in H_lt. lia.
    + destruct prefix as [|z2 prefix].
      * inversion H_eq; subst. simpl in H_lt. lia.
      * destruct prefix as [|z3 prefix].
        -- inversion H_eq; subst. simpl in H_lt. lia.
        -- destruct prefix as [|z4 prefix].
           ++ inversion H_eq; subst. simpl in H_lt. lia.
           ++ destruct prefix as [|z5 prefix].
              ** inversion H_eq; subst. simpl in H_lt. lia.
              ** inversion H_eq.
  - intros H. discriminate H.
Qed.