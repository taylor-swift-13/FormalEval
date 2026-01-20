Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool.
Open Scope Z_scope.

Fixpoint sum_even_at_odd_indices (l : list Z) (n : nat) : Z :=
  match l with
  | nil => 0%Z
  | h :: t =>
      if andb (Nat.odd n) (Z.even h)
      then (h + sum_even_at_odd_indices t (S n))%Z
      else sum_even_at_odd_indices t (S n)
  end.

Definition add_impl (lst : list Z) : Z := sum_even_at_odd_indices lst 0.

Example add_impl_ex: add_impl (4%Z :: 2%Z :: 6%Z :: 7%Z :: nil) = 2%Z.
Proof. reflexivity. Qed.

Definition add_spec (lst : list Z) (output : Z) : Prop :=
  output = add_impl lst.


