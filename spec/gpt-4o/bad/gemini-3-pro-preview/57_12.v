Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition monotonic_spec (l : list nat) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, i < j < length l -> nth i l 0 <= nth j l 0) \/
    (forall i j, i < j < length l -> nth i l 0 >= nth j l 0).

Fixpoint check_incr (l : list nat) : bool :=
  match l with
  | [] => true
  | x :: xs => 
    match xs with
    | [] => true
    | y :: _ => (x <=? y) && check_incr xs
    end
  end.

Lemma check_incr_correct : forall l, check_incr l = true ->
  forall i j, i < j < length l -> nth i l 0 <= nth j l 0.
Proof.
  induction l as [|x xs IH]; intros Hsorted i j Hrange.
  - simpl in Hrange; lia.
  - destruct xs as [|y ys].
    + simpl in Hrange; lia.
    + simpl in Hsorted.
      apply andb_prop in Hsorted. destruct Hsorted as [Hxy Hsorted_xs].
      apply Nat.leb_le in Hxy.
      destruct i.
      * simpl. destruct j.
        -- lia.
        -- simpl. destruct j.
           ++ simpl. assumption.
           ++ simpl. 
              apply Nat.le_trans with y.
              ** assumption.
              ** apply (IH Hsorted_xs 0 (S j)).
                 simpl in Hrange. lia.
      * simpl. destruct j.
        -- lia.
        -- simpl. apply IH.
           ++ assumption.
           ++ simpl in Hrange. lia.
Qed.

Example test_monotonic_1_1_2_3_3_3_4_5 : monotonic_spec [1; 1; 2; 3; 3; 3; 4; 5] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    left.
    apply check_incr_correct.
    vm_compute. reflexivity.
  - intros _.
    reflexivity.
Qed.