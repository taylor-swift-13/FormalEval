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

Definition extract_integers_from_mixed (lst : list (Z + R)) : list Z :=
  fold_right (fun x acc => match x with inl z => z :: acc | inr _ => acc end) nil lst.

Example test_mixed_list : double_the_difference_spec (extract_integers_from_mixed 
  (inr 2.5%R :: inr 3.7%R :: inl (-5)%Z :: inl 7%Z :: inr 10.5%R :: inl (-11)%Z :: 
   inr (-12.8)%R :: inl (-14)%Z :: inr 3.578420498601563%R :: inr (-15.3)%R :: 
   inl (-16)%Z :: inl 19%Z :: inr 20.2%R :: inr (-23.8)%R :: inl 24%Z :: inl 25%Z :: 
   inl 26%Z :: inr (-27.5)%R :: inl (-28)%Z :: inr 3.7%R :: inr 10.5%R :: nil)) 1035%Z.
Proof.
  unfold double_the_difference_spec.
  unfold extract_integers_from_mixed.
  simpl.
  reflexivity.
Qed.