Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool.
Import ListNotations.
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

Definition problem_85_pre (lst : list Z) : Prop := lst <> []%list.

Definition problem_85_spec (lst : list Z) (output : Z) : Prop :=
  output = add_impl lst.

Example problem_85_test_case :
  problem_85_spec [1%Z; 5%Z; 1%Z; 9%Z; 12%Z; 15%Z; 18%Z; 5%Z] 0%Z.
Proof.
  unfold problem_85_spec, add_impl.
  simpl.
  reflexivity.
Qed.