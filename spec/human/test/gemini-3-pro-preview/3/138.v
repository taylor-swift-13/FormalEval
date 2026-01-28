Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_new: problem_3_spec [99; 100; -50; 20; -10] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|x1 prefix].
    + simpl in Hlt. lia.
    + injection Happ as Hx1 Happ. subst x1.
      destruct prefix as [|x2 prefix].
      * simpl in Hlt. lia.
      * injection Happ as Hx2 Happ. subst x2.
        destruct prefix as [|x3 prefix].
        -- simpl in Hlt. lia.
        -- injection Happ as Hx3 Happ. subst x3.
           destruct prefix as [|x4 prefix].
           ++ simpl in Hlt. lia.
           ++ injection Happ as Hx4 Happ. subst x4.
              destruct prefix as [|x5 prefix].
              ** simpl in Hlt. lia.
              ** injection Happ as Hx5 Happ. subst x5.
                 destruct prefix as [|x6 prefix].
                 --- simpl in Hlt. lia.
                 --- discriminate Happ.
  - intros H. discriminate H.
Qed.