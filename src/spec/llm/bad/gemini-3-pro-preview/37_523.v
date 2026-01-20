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
  [5; 2; -13; 3; -5; 2; -10; -3; -2; 3; -8; 0; -7; -5; 1; -10; -9; 3] 
  [-13; 2; -10; 3; -9; 2; -8; -3; -7; 3; -5; 0; -2; -5; 1; -10; 5; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We destruct i 18 times to cover all indices 0..17 *)
      do 18 (destruct i; [ simpl in *; try discriminate; reflexivity | ]).
      (* For i >= 18 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Since the lists are concrete and have no duplicates, we can use Permutation_NoDup *)
        apply Permutation_NoDup.
        -- (* NoDup input *)
           repeat (constructor; [ intro H; simpl in H; repeat (destruct H as [H|H]; [ discriminate | ]); try contradiction | ]).
           apply NoDup_nil.
        -- (* NoDup output *)
           repeat (constructor; [ intro H; simpl in H; repeat (destruct H as [H|H]; [ discriminate | ]); try contradiction | ]).
           apply NoDup_nil.
        -- (* Elements match *)
           intros x; split; intro H;
           repeat (destruct H as [H|H]; [ subst; simpl; tauto | ]); try contradiction.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.