Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_43_pre (input : list Z) : Prop := True.

Definition problem_43_spec (input : list Z) (output : bool) : Prop :=
  (exists i j : nat,
    (i <> j)  /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (nth i input 0 + nth j input 0 = 0))
  <-> (output = true).

Example problem_43_example_1 :
  problem_43_spec [1%Z; 3%Z; 5%Z; 0%Z] false.
Proof.
  unfold problem_43_spec.
  split.
  - intros [i [j [Hij [Hi [Hj Hsum]]]]].
    exfalso.
    simpl in Hi, Hj.
    (* length is 4 *)
    destruct i as [|i1].
    + (* i = 0, value = 1 *)
      simpl in Hsum.
      destruct j as [|j1]; simpl in *; try lia.
      destruct j1 as [|j2]; simpl in *; try lia.
      destruct j2 as [|j3]; simpl in *; try lia.
      destruct j3 as [|j4]; simpl in *; try lia.
    + destruct i1 as [|i2].
      * (* i = 1, value = 3 *)
        simpl in Hsum.
        destruct j as [|j1]; simpl in *; try lia.
        destruct j1 as [|j2]; simpl in *; try lia.
        destruct j2 as [|j3]; simpl in *; try lia.
        destruct j3 as [|j4]; simpl in *; try lia.
      * destruct i2 as [|i3].
        -- (* i = 2, value = 5 *)
           simpl in Hsum.
           destruct j as [|j1]; simpl in *; try lia.
           destruct j1 as [|j2]; simpl in *; try lia.
           destruct j2 as [|j3]; simpl in *; try lia.
           destruct j3 as [|j4]; simpl in *; try lia.
        -- destruct i3 as [|i4].
           ++ (* i = 3, value = 0 *)
              simpl in Hsum.
              destruct j as [|j1]; simpl in *; try lia.
              destruct j1 as [|j2]; simpl in *; try lia.
              destruct j2 as [|j3]; simpl in *; try lia.
              destruct j3 as [|j4]; simpl in *.
              ** (* j = 3, value = 0, violates i <> j *)
                 apply Hij. reflexivity.
              ** lia.
           ++ (* i >= 4, contradicts Hi *)
              lia.
  - intros Hfeq.
    exfalso. discriminate Hfeq.
Qed.