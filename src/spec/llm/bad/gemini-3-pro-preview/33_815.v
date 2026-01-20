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

Fixpoint remove_first (x : Z) (l : list Z) : option (list Z) :=
  match l with
  | [] => None
  | y :: tl => if x =? y then Some tl 
               else match remove_first x tl with
                    | Some rest => Some (y :: rest)
                    | None => None
                    end
  end.

Lemma remove_first_perm : forall x l l',
  remove_first x l = Some l' -> Permutation l (x :: l').
Proof.
  intros x l. induction l; simpl; intros.
  - discriminate.
  - destruct (x =? a) eqn:E.
    + injection H; intro; subst. apply Z.eqb_eq in E. subst. constructor. apply Permutation_refl.
    + destruct (remove_first x l) eqn:E2; try discriminate.
      injection H; intro; subst.
      apply Permutation_trans with (a :: x :: l0).
      * apply perm_skip. apply IHl. reflexivity.
      * apply perm_swap.
Qed.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 8; 15; 7; 3; 4; 5; 700; 900; 799; -200; -901; 800; 1000; 4; 8; 5]
  [5; 500; 6; 7; 8; 289; 7; -105; -277; 8; 8; 15; 20; 3; 4; 104; 700; 900; 300; -200; -901; 799; 1000; 4; 800; 5].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 26 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        repeat (eapply Permutation_trans; 
          [ apply Permutation_cons | 
            apply Permutation_sym; apply remove_first_perm; reflexivity ]).
        apply Permutation_nil.
      * simpl.
        repeat (constructor; [ simpl; try lia | ]).
        constructor.
Qed.