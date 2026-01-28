Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
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

Example test_case : sort_third_spec 
  [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; -901; 20; 3; 6; 8]
  [-901; 6; 7; 4; 8; 289; 8; -105; -277; 20; 200; 3; 20; 700; 900; 104; 800; -901; 290; 3; 6; 300].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We iterate through the indices to check each case.
         For indices divisible by 3, H yields a contradiction.
         For others, we check equality. *)
      do 22 (destruct i; [ simpl in H; try contradiction; simpl; reflexivity | ]).
      (* For i >= 22, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Tactic to prove permutation for concrete lists by moving matching elements to front *)
        Ltac solve_perm :=
          match goal with
          | |- Permutation [] [] => apply Permutation_nil
          | |- Permutation (?x :: ?tl) ?tr =>
              let rec find_split l pre :=
                match l with
                | x :: ?post => constr:((pre, post))
                | ?y :: ?post => find_split post (pre ++ [y])
                end
              in
              let pair := find_split tr (@nil Z) in
              match pair with
              | (?pre, ?post) =>
                  transitivity (x :: (pre ++ post));
                  [ apply Permutation_cons_app with (l1 := pre) (l2 := post)
                  | apply perm_skip; solve_perm ]
              end
          end.
        solve_perm.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply Z.leb_le; reflexivity) ]).
        apply Sorted_nil.
Qed.