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

Example test_case_85 : problem_85_spec [11%Z; 8%Z; 89%Z; 33%Z; 66%Z; 67%Z; 88%Z; 99%Z; 100%Z] 8%Z.
Proof.
  unfold problem_85_spec.
  unfold add_impl.
  simpl.
  reflexivity.
Qed.