Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Ltac find_elem x l :=
  match l with
  | x :: _ => constr:(@nil Z)
  | ?y :: ?tl => 
      let rest := find_elem x tl in
      constr:(y :: rest)
  end.

Ltac solve_perm :=
  simpl;
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?tl) ?r =>
      let l1 := find_elem x r in
      apply Permutation_cons_app with (l1 := l1);
      solve_perm
  end.

Ltac solve_index :=
  intros i H;
  do 25 (destruct i as [|i]; 
    [ simpl in *; 
      try (exfalso; compute in H; discriminate); 
      reflexivity 
    | ]);
  simpl; reflexivity.

Ltac solve_sorted :=
  repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (constructor; lia) ]);
  apply Sorted_nil.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 290; 8; 289; 20; 104; -277; 8; 104; 200; -8; 700; 900; -901; 800; 1000; 290; -8; 104] 
  [-277; 500; 6; 7; 290; 8; 104; 20; 104; 200; 8; 104; 289; -8; 700; 300; -901; 800; 900; 290; -8; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Indices *)
      solve_index.
    + split.
      * (* Permutation *)
        solve_perm.
      * (* Sorted *)
        solve_sorted.
Qed.