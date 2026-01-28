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

Example test_problem_43 : problem_43_spec [1; 3; 5; 0] false.
Proof.
  unfold problem_43_spec.
  split; intro H.
  - (* Forward direction: (Exists ...) -> false = true *)
    destruct H as [i [j [Hneq [Hi [Hj Hsum]]]]].
    simpl in Hi, Hj.
    (* We iterate through all possible indices for i (0 to 3) *)
    destruct i as [|i].
    { (* i = 0 *)
      destruct j as [|j].
      { (* j = 0 *) lia. } (* i <> j contradiction *)
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. } (* 1 + 3 <> 0 *)
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. } (* 1 + 5 <> 0 *)
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. } (* 1 + 0 <> 0 *)
      lia. (* j >= 4 contradiction *)
    }
    destruct i as [|i].
    { (* i = 1 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. } (* 3 + 1 <> 0 *)
      destruct j as [|j].
      { (* j = 1 *) lia. }
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. } (* 3 + 5 <> 0 *)
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. } (* 3 + 0 <> 0 *)
      lia.
    }
    destruct i as [|i].
    { (* i = 2 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. } (* 5 + 1 <> 0 *)
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. } (* 5 + 3 <> 0 *)
      destruct j as [|j].
      { (* j = 2 *) lia. }
      destruct j as [|j].
      { (* j = 3 *) simpl in Hsum. lia. } (* 5 + 0 <> 0 *)
      lia.
    }
    destruct i as [|i].
    { (* i = 3 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. } (* 0 + 1 <> 0 *)
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. } (* 0 + 3 <> 0 *)
      destruct j as [|j].
      { (* j = 2 *) simpl in Hsum. lia. } (* 0 + 5 <> 0 *)
      destruct j as [|j].
      { (* j = 3 *) lia. }
      lia.
    }
    (* i >= 4 *)
    lia.
  - (* Backward direction: false = true -> Exists ... *)
    discriminate H.
Qed.