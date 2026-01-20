
Require Import List.
Import ListNotations.
Require Import Nat.

Definition is_palindrome (l : list nat) : Prop :=
  l = rev l.

Definition will_it_fly_spec (q : list nat) (w : nat) (res : bool) : Prop :=
  res = (if andb (Bool.eqb q (rev q)) (leb (fold_left Nat.add q 0) w)
         then true else false).
