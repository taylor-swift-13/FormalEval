Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1; 1; 1; 1; 4; 1] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|z1 prefix].
    + simpl in Hlt. lia.
    + destruct prefix as [|z2 prefix].
      * simpl in Happ. injection Happ as Hz1 _. subst. simpl in Hlt. lia.
      * destruct prefix as [|z3 prefix].
        -- simpl in Happ. injection Happ as Hz1 Hz2 _. subst. simpl in Hlt. lia.
        -- destruct prefix as [|z4 prefix].
           ++ simpl in Happ. injection Happ as Hz1 Hz2 Hz3 _. subst. simpl in Hlt. lia.
           ++ destruct prefix as [|z5 prefix].
              ** simpl in Happ. injection Happ as Hz1 Hz2 Hz3 Hz4 _. subst. simpl in Hlt. lia.
              ** destruct prefix as [|z6 prefix].
                 --- simpl in Happ. injection Happ as Hz1 Hz2 Hz3 Hz4 Hz5 _. subst. simpl in Hlt. lia.
                 --- destruct prefix as [|z7 prefix].
                     +++ simpl in Happ. injection Happ as Hz1 Hz2 Hz3 Hz4 Hz5 Hz6 _. subst. simpl in Hlt. lia.
                     +++ simpl in Happ. discriminate.
  - intros H. discriminate H.
Qed.