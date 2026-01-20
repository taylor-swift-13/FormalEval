Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [5; 3; -5; 23; -3; 3; 4; -9; 0; 123; 1; -10] 
  [-5; 3; -3; 23; 0; 3; 1; -9; 4; 123; 5; -10].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 12 (destruct i as [|i]; [ 
        simpl in Hodd; try discriminate; simpl; reflexivity 
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation check *)
        simpl.
        (* l_even = [5; -5; -3; 4; 0; 1] *)
        (* r_even = [-5; -3; 0; 1; 4; 5] *)
        eapply perm_trans. { apply perm_swap. } (* [-5; 5; -3; 4; 0; 1] *)
        apply perm_skip.
        eapply perm_trans. { apply perm_swap. } (* [-3; 5; 4; 0; 1] *)
        apply perm_skip.
        eapply perm_trans. { apply perm_skip. apply perm_swap. } (* [5; 0; 4; 1] *)
        eapply perm_trans. { apply perm_swap. } (* [0; 5; 4; 1] *)
        apply perm_skip.
        eapply perm_trans. { apply perm_skip. apply perm_swap. } (* [5; 1; 4] *)
        eapply perm_trans. { apply perm_swap. } (* [1; 5; 4] *)
        apply perm_skip.
        apply perm_swap.
      * (* Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; lia ]).
        apply Sorted_nil.
Qed.