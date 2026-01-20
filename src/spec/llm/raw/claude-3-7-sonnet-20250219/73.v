
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition palindrome {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
           (l : list A) : Prop :=
  l = rev l.

Definition smallest_change_spec {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
           (arr : list A) (changes : nat) : Prop :=
  exists arr', palindrome eq_dec arr' /\
              length arr' = length arr /\
              changes = (fix count_diff l1 l2 :=
                           match l1, l2 with
                           | [], [] => 0
                           | x::xs, y::ys => (if eq_dec x y then 0 else 1) + count_diff xs ys
                           | _, _ => 0
                           end) arr (rev arr) /\
              (forall i, (i < length arr)%nat ->
                         (nth i arr' arr (i) = nth i arr arr default) \/
                         changes > 0).
