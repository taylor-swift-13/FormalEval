
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.

Open Scope Z_scope.

Fixpoint digits_of_positive (n : positive) : list Z :=
  match n with
  | xH => [1]
  | xO p => (Z.pos n mod 10) :: digits_of_positive (Pos.div n 10)
  | xI p => (Z.pos n mod 10) :: digits_of_positive (Pos.div n 10)
  end.

Definition signed_digits (x : Z) : list Z :=
  match x with
  | Z0 => [0]
  | Zpos p => rev (digits_of_positive p)
  | Zneg p => 
      let d := rev (digits_of_positive p) in
      match d with
      | [] => []
      | h :: t => (-h) :: t
      end
  end.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition sum_of_signed_digits (x : Z) : Z :=
  sum_list (signed_digits x).

Definition judge (x : Z) : Z :=
  if Z.gtb (sum_of_signed_digits x) 0 then 1 else 0.

Definition count_nums_spec (arr : list Z) (result : Z) : Prop :=
  result = fold_right Z.add 0 (map judge arr).
