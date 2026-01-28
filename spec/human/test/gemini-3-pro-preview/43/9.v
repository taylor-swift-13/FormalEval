Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `pairs_sum_to_zero` *)
Definition problem_43_pre (input : list Z) : Prop := True.

Definition problem_43_spec (input : list Z) (output : bool) : Prop :=
  (exists i j : nat,
    (i <> j)  /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (nth i input 0 + nth j input 0 = 0))
  <-> (output = true).

Example test_problem_43 : problem_43_spec [-3; 9; -1; 4; 2; 31] false.
Proof.
  unfold problem_43_spec.
  split; intro H.
  - destruct H as [i [j [Hneq [Hi [Hj Hsum]]]]].
    simpl in Hi, Hj.
    destruct i as [|i].
    { (* i = 0 *)
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      lia.
    }
    destruct i as [|i].
    { (* i = 1 *)
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      lia.
    }
    destruct i as [|i].
    { (* i = 2 *)
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      lia.
    }
    destruct i as [|i].
    { (* i = 3 *)
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      lia.
    }
    destruct i as [|i].
    { (* i = 4 *)
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      lia.
    }
    destruct i as [|i].
    { (* i = 5 *)
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [simpl in Hsum; lia|].
      destruct j as [|j]; [lia|].
      lia.
    }
    lia.
  - discriminate H.
Qed.