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

Example test_case_1 : problem_9_spec 
  [10; 5; 20; 30; 25; 20; 15; 10; 15] 
  [10; 10; 20; 30; 30; 30; 30; 30; 30].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    repeat (destruct i as [|i]; [| try (simpl in Hi; lia) ]).
    (* i = 0 *)
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; try lia|]); try lia.
      - exists 0%nat. split; [lia|reflexivity]. }
    (* i = 1 *)
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; try lia|]); try lia.
      - exists 0%nat. split; [lia|reflexivity]. }
    (* i = 2 *)
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; try lia|]); try lia.
      - exists 2%nat. split; [lia|reflexivity]. }
    (* i = 3 *)
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; try lia|]); try lia.
      - exists 3%nat. split; [lia|reflexivity]. }
    (* i = 4 *)
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; try lia|]); try lia.
      - exists 3%nat. split; [lia|reflexivity]. }
    (* i = 5 *)
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; try lia|]); try lia.
      - exists 3%nat. split; [lia|reflexivity]. }
    (* i = 6 *)
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; try lia|]); try lia.
      - exists 3%nat. split; [lia|reflexivity]. }
    (* i = 7 *)
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; try lia|]); try lia.
      - exists 3%nat. split; [lia|reflexivity]. }
    (* i = 8 *)
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; try lia|]); try lia.
      - exists 3%nat. split; [lia|reflexivity]. }
Qed.