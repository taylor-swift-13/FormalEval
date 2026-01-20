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

Definition filter_integers (lst : list (Z + R)) : list Z :=
  fold_right (fun x acc => match x with inl z => z :: acc | inr _ => acc end) nil lst.

Definition double_the_difference_mixed_spec (lst : list (Z + R)) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers (filter_integers lst).

Example test_mixed_list : double_the_difference_mixed_spec 
  (inr 3.7%R :: inl (-5)%Z :: inl 7%Z :: inr 10.5%R :: inl (-11)%Z :: 
   inr (-12.8)%R :: inl (-14)%Z :: inr (-15.3)%R :: inl (-16)%Z :: inl 19%Z :: 
   inr 20.2%R :: inr 21.9%R :: inr 1.0850617393937045%R :: inr (-31.65305994277872)%R :: 
   inl 24%Z :: inl 25%Z :: inl 6%Z :: inr 2.968032886251095%R :: inl 5%Z :: nil) 
  1060%Z.
Proof.
  unfold double_the_difference_mixed_spec.
  unfold filter_integers.
  simpl.
  unfold sum_of_squares_of_positive_odd_integers.
  unfold is_positive_odd_integer.
  simpl.
  reflexivity.
Qed.