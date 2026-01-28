Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example test_case_new : problem_9_spec [3; 2; 3; 100; 3] [3; 3; 3; 100; 100].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i].
    { (* i = 0 *)
      split.
      - intros j Hj. do 1 (destruct j as [|j]; [simpl; lia|]). simpl in Hj; lia.
      - exists 0%nat. split. lia. reflexivity.
    }
    destruct i as [|i].
    { (* i = 1 *)
      split.
      - intros j Hj. do 2 (destruct j as [|j]; [simpl; lia|]). simpl in Hj; lia.
      - exists 0%nat. split. lia. reflexivity.
    }
    destruct i as [|i].
    { (* i = 2 *)
      split.
      - intros j Hj. do 3 (destruct j as [|j]; [simpl; lia|]). simpl in Hj; lia.
      - exists 0%nat. split. lia. reflexivity.
    }
    destruct i as [|i].
    { (* i = 3 *)
      split.
      - intros j Hj. do 4 (destruct j as [|j]; [simpl; lia|]). simpl in Hj; lia.
      - exists 3%nat. split. lia. reflexivity.
    }
    destruct i as [|i].
    { (* i = 4 *)
      split.
      - intros j Hj. do 5 (destruct j as [|j]; [simpl; lia|]). simpl in Hj; lia.
      - exists 3%nat. split. lia. reflexivity.
    }
    (* i >= 5 *)
    simpl in Hi. lia.
Qed.