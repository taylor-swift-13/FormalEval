Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

(* Definition from specification *)
Inductive collatz_list (n : Z) : list Z -> Prop :=
  | cl_one : n = 1 -> collatz_list n [1]
  | cl_even : forall l',
      n > 1 ->
      Z.even n = true ->
      collatz_list (n / 2) l' ->
      collatz_list n (n :: l')
  | cl_odd : forall l',
      n > 1 ->
      Z.odd n = true ->
      collatz_list (3 * n + 1) l' ->
      collatz_list n (n :: l').

Definition problem_123_pre (n : Z) : Prop := n > 0.

Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists (c_seq : list Z),
    collatz_list n c_seq /\
    Permutation result (filter (fun x => Z.odd x) c_seq) /\
    Sorted Z.le result.

(* Test case to prove *)
Example test_14 : problem_123_spec 14 [1; 5; 7; 11; 13; 17].
Proof.
  unfold problem_123_spec.
  (* Provide the witness: the full Collatz sequence for 14 *)
  exists [14; 7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
  
  split.
  - (* Subgoal 1: Prove this is a valid collatz_list *)
    apply cl_even; [lia | reflexivity | ]. (* 14 -> 7 *)
    apply cl_odd;  [lia | reflexivity | ]. (* 7 -> 22 *)
    apply cl_even; [lia | reflexivity | ]. (* 22 -> 11 *)
    apply cl_odd;  [lia | reflexivity | ]. (* 11 -> 34 *)
    apply cl_even; [lia | reflexivity | ]. (* 34 -> 17 *)
    apply cl_odd;  [lia | reflexivity | ]. (* 17 -> 52 *)
    apply cl_even; [lia | reflexivity | ]. (* 52 -> 26 *)
    apply cl_even; [lia | reflexivity | ]. (* 26 -> 13 *)
    apply cl_odd;  [lia | reflexivity | ]. (* 13 -> 40 *)
    apply cl_even; [lia | reflexivity | ]. (* 40 -> 20 *)
    apply cl_even; [lia | reflexivity | ]. (* 20 -> 10 *)
    apply cl_even; [lia | reflexivity | ]. (* 10 -> 5 *)
    apply cl_odd;  [lia | reflexivity | ]. (* 5 -> 16 *)
    apply cl_even; [lia | reflexivity | ]. (* 16 -> 8 *)
    apply cl_even; [lia | reflexivity | ]. (* 8 -> 4 *)
    apply cl_even; [lia | reflexivity | ]. (* 4 -> 2 *)
    apply cl_even; [lia | reflexivity | ]. (* 2 -> 1 *)
    apply cl_one;  [reflexivity].          (* 1 *)

  - split.
    + (* Subgoal 2: Prove Permutation *)
      simpl. (* Evaluates the filter to [7; 11; 17; 13; 5; 1] *)
      (* We need to prove Permutation [1; 5; 7; 11; 13; 17] [7; 11; 17; 13; 5; 1] *)
      apply NoDup_Permutation.
      * (* Proof of NoDup for result *)
        repeat (constructor; [ intro H; simpl in H; repeat destruct H as [H|H]; try lia | ]).
      * (* Proof of NoDup for filtered sequence *)
        repeat (constructor; [ intro H; simpl in H; repeat destruct H as [H|H]; try lia | ]).
      * (* Proof that elements are the same *)
        intros x. split; intro H.
        -- (* Forward direction *)
           simpl in H; repeat destruct H as [H|H]; subst; simpl; tauto.
        -- (* Backward direction *)
           simpl in H; repeat destruct H as [H|H]; subst; simpl; tauto.

    + (* Subgoal 3: Prove Sorted *)
      repeat (constructor; simpl; try lia).
Qed.