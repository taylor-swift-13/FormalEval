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

Example test_problem_43 : problem_43_spec [1; 3; -2; 1] false.
Proof.
  unfold problem_43_spec.
  split; intro H.
  - (* Forward direction: (Exists ...) -> false = true *)
    destruct H as [i [j [Hneq [Hi [Hj Hsum]]]]].
    simpl in Hi, Hj.
    destruct i as [|i].
    { (* i = 0 *)
      destruct j as [|j].
      { (* j = 0 *) lia. } (* i <> j *)
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. } (* 1 + 3 <> 0 *)
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. } (* 1 + -2 <> 0 *)
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. } (* 1 + 1 <> 0 *)
      lia. (* j >= 4 *)
    }
    destruct i as [|i].
    { (* i = 1 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. } (* 3 + 1 <> 0 *)
      destruct j as [|j].
      { (* j = 1 *) lia. } (* i <> j *)
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. } (* 3 + -2 <> 0 *)
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. } (* 3 + 1 <> 0 *)
      lia.
    }
    destruct i as [|i].
    { (* i = 2 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. } (* -2 + 1 <> 0 *)
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. } (* -2 + 3 <> 0 *)
      destruct j as [|j].
      { (* j = 2 *) lia. } (* i <> j *)
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. } (* -2 + 1 <> 0 *)
      lia.
    }
    destruct i as [|i].
    { (* i = 3 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. } (* 1 + 1 <> 0 *)
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. } (* 1 + 3 <> 0 *)
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. } (* 1 + -2 <> 0 *)
      destruct j as [|j].
      { (* j = 3 *) lia. } (* i <> j *)
      lia.
    }
    (* i >= 4 *)
    lia.
  - (* Backward direction: false = true -> Exists ... *)
    discriminate H.
Qed.