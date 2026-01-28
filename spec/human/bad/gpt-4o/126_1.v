Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

(* Definition of is_sorted function *)
Fixpoint is_sorted (l : list nat) : bool :=
  match l with
  | [] => true
  | [x] => true
  | x :: y :: xs =>
      if Nat.eqb x y then false
      else if Nat.ltb x y then is_sorted (y :: xs)
      else false
  end.

(* Corrected problem specification including duplicates handling *)
Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l /\ (forall x, count_occ Nat.eq_dec l x <= 2) <-> b = true.

(* Example proof *)
Example test_is_sorted_5 : problem_126_spec [5] true.
Proof.
  unfold problem_126_spec.
  simpl.
  split.
  - intros [Hsorted Hcount].
    reflexivity.
  - intros H.
    split.
    + repeat constructor.
    + intros x.
      simpl.
      destruct (Nat.eq_dec 5 x); lia.
Qed.