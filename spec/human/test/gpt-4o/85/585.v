Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
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

Example test_case_1 : problem_85_spec [3%Z; 1%Z; 2%Z; 7%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 17%Z; 8%Z; 9%Z; 10%Z; 10%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 99%Z; 18%Z; 19%Z; 20%Z; 3%Z; 3%Z; 12%Z] 32%Z.
Proof.
  unfold problem_85_spec, add_impl.
  simpl.
  unfold sum_even_at_odd_indices.
  simpl.
  reflexivity.
Qed.