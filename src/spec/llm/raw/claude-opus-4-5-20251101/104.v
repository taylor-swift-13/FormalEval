
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Open Scope Z_scope.

Fixpoint digits (n : Z) : list Z :=
  if Z.leb n 0 then []
  else (Z.modulo n 10) :: digits (Z.div n 10).

Definition has_even_digit (n : Z) : bool :=
  existsb (fun d => Z.even d) (digits n).

Definition all_odd_digits (n : Z) : Prop :=
  forall d, In d (digits n) -> Z.odd d = true.

Definition unique_digits_spec (x : list Z) (result : list Z) : Prop :=
  (forall n, In n result <-> (In n x /\ all_odd_digits n)) /\
  Sorted Z.le result.
