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

Ltac solve_perm :=
  simpl;
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?tl) ?r =>
    let rec find_x l1 l2 :=
      match l2 with
      | ?z :: ?rest =>
          first [ 
            constr_eq z x; 
            apply (Permutation_cons_app _ tl l1 rest x);
            [ solve_perm | simpl; reflexivity ]
          | find_x (app l1 (cons z nil)) rest
          ]
      end
    in find_x (@nil Z) r
  end.

Example test_sort_even_case : sort_even_spec 
  [4; 2; 2; 0; 9; 5; -3; 2; 8; 3; 7; 2; 2; 8; 2; 2; 2] 
  [-3; 2; 2; 0; 2; 5; 2; 2; 2; 3; 4; 2; 7; 8; 8; 2; 9].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 18 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        solve_perm.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try apply HdRel_cons; simpl; lia ]).
        apply Sorted_nil.
Qed.