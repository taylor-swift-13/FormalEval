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

Example test_problem_43 : problem_43_spec [2; 3; 4; 5; -9] false.
Proof.
  unfold problem_43_spec.
  split; intro H.
  - (* Forward direction: (Exists ...) -> false = true *)
    destruct H as [i [j [Hneq [Hi [Hj Hsum]]]]].
    simpl in Hi, Hj.
    destruct i as [|i].
    { (* i = 0, val = 2 *)
      destruct j as [|j].
      { (* j = 0 *) lia. }
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 4 *) simpl in Hsum. lia. }
      lia.
    }
    destruct i as [|i].
    { (* i = 1, val = 3 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 1 *) lia. }
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 4 *) simpl in Hsum. lia. }
      lia.
    }
    destruct i as [|i].
    { (* i = 2, val = 4 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 2 *) lia. }
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 4 *) simpl in Hsum. lia. }
      lia.
    }
    destruct i as [|i].
    { (* i = 3, val = 5 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 3 *) lia. }
      destruct j as [|j].
      { (* j = 4 *) simpl in Hsum. lia. }
      lia.
    }
    destruct i as [|i].
    { (* i = 4, val = -9 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. }
      destruct j as [|j].
      { (* j = 4 *) lia. }
      lia.
    }
    (* i >= 5 *)
    lia.
  - (* Backward direction: false = true -> Exists ... *)
    discriminate H.
Qed.