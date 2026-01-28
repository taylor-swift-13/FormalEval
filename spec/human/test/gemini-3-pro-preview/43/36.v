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

Example test_problem_43 : problem_43_spec [0; 1] false.
Proof.
  unfold problem_43_spec.
  split; intro H.
  - (* Forward direction: (Exists ...) -> false = true *)
    destruct H as [i [j [Hneq [Hi [Hj Hsum]]]]].
    simpl in Hi, Hj.
    destruct i as [|i].
    { (* i = 0 *)
      destruct j as [|j].
      { (* j = 0 *) lia. } (* i <> j contradiction *)
      destruct j as [|j].
      { (* j = 1 *) simpl in Hsum. lia. } (* 0 + 1 <> 0 *)
      lia. (* j >= 2 contradiction *)
    }
    destruct i as [|i].
    { (* i = 1 *)
      destruct j as [|j].
      { (* j = 0 *) simpl in Hsum. lia. } (* 1 + 0 <> 0 *)
      destruct j as [|j].
      { (* j = 1 *) lia. } (* i <> j contradiction *)
      lia. (* j >= 2 contradiction *)
    }
    lia. (* i >= 2 contradiction *)
  - (* Backward direction: false = true -> Exists ... *)
    discriminate H.
Qed.