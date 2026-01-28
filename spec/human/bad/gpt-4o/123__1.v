(* Import Coq standard libraries *)
Require Import Coq.ZArith.ZArith.   (* Integer arithmetic *)
Require Import Coq.Lists.List.      (* List operations *)
Require Import Coq.Sorting.Permutation. (* List permutation relations *)
Require Import Coq.Sorting.Sorted.      (* List sorting predicates *)

Require Import Lia. (* Import the Lia library for linear integer arithmetic *)

Import ListNotations.
Open Scope Z_scope.

(* Inductive predicate defining the Collatz sequence *)
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

(* Precondition: n must be a positive integer *)
Definition problem_123_pre (n : Z) : Prop := n > 0.

(* Specification: relation between input n and output result *)
Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists (c_seq : list Z),
    collatz_list n c_seq /\
    Permutation result (filter (fun x => Z.odd x) c_seq) /\
    Sorted Z.le result.

(* Example test case proof *)
Example problem_123_test : problem_123_spec 14 [1; 5; 7; 11; 13; 17].
Proof.
  unfold problem_123_spec.
  exists [14; 7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
  split.
  - (* Prove that it is a Collatz sequence *)
    apply cl_even.
    + lia.
    + reflexivity.
    + apply cl_odd.
      * lia.
      * reflexivity.
      * apply cl_even.
        -- lia.
        -- reflexivity.
        -- apply cl_odd.
           ++ lia.
           ++ reflexivity.
           ++ apply cl_even.
              ** lia.
              ** reflexivity.
              ** apply cl_odd.
                 --- lia.
                 --- reflexivity.
                 --- apply cl_even.
                     *** lia.
                     *** reflexivity.
                     *** apply cl_even.
                         +++ lia.
                         +++ reflexivity.
                         +++ apply cl_odd.
                             --- lia.
                             --- reflexivity.
                             --- apply cl_odd.
                                 +++ lia.
                                 +++ reflexivity.
                                 +++ apply cl_even.
                                     *** lia.
                                     *** reflexivity.
                                     *** apply cl_even.
                                         +++ lia.
                                         +++ reflexivity.
                                         +++ apply cl_odd.
                                             --- lia.
                                             --- reflexivity.
                                             --- apply cl_even.
                                                 *** lia.
                                                 *** reflexivity.
                                                 *** apply cl_even.
                                                     +++ lia.
                                                     +++ reflexivity.
                                                     +++ apply cl_odd.
                                                         --- lia.
                                                         --- reflexivity.
                                                         --- apply cl_one.
                                                             lia.
  - (* Prove that the result is a permutation of the odd numbers from the Collatz sequence and is sorted *)
    split.
    + unfold filter. simpl.
      apply Permutation_cons_app.
      apply Permutation_cons_app.
      apply Permutation_cons_app.
      apply Permutation_cons_app.
      apply Permutation_cons_app.
      apply Permutation_cons_app.
      apply Permutation_refl.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_cons.
                 --- apply Sorted_cons.
                     *** apply Sorted_nil.
                     *** lia.
                 --- lia.
              ** lia.
           ++ lia.
        -- lia.
      * lia.
Qed.