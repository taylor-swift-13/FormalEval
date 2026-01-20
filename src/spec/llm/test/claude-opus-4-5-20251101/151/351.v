Require Import ZArith.
Require Import List.
Require Import Reals.
Open Scope Z_scope.

Definition is_positive_odd_integer (n : Z) : bool :=
  (n >? 0) && (n mod 2 =? 1).

Fixpoint sum_of_squares_of_positive_odd_integers (lst : list Z) : Z :=
  match lst with
  | nil => 0
  | x :: xs => if is_positive_odd_integer x 
               then x * x + sum_of_squares_of_positive_odd_integers xs
               else sum_of_squares_of_positive_odd_integers xs
  end.

Definition double_the_difference_spec (lst : list Z) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers lst.

Definition extract_integers (mixed_list : list (Z + R)) : list Z :=
  fold_right (fun x acc => match x with inl z => z :: acc | inr _ => acc end) nil mixed_list.

Example test_mixed_list : double_the_difference_spec (extract_integers (inr 3.7%R :: inl (-5)%Z :: inl 7%Z :: inr 10.5%R :: inl (-11)%Z :: inr (-12.8)%R :: inl (-14)%Z :: inr (-15.3)%R :: inl (-16)%Z :: inl 19%Z :: inr 20.2%R :: inr 21.9%R :: inr (-28.06693171025116)%R :: inl 24%Z :: inr 4.98%R :: inl 6%Z :: inr (-27.5)%R :: inl (-28)%Z :: inl 5%Z :: inl (-28)%Z :: nil)) 435%Z.
Proof.
  unfold double_the_difference_spec.
  unfold extract_integers.
  simpl.
  unfold is_positive_odd_integer.
  simpl.
  reflexivity.
Qed.