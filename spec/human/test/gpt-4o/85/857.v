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

Example test_case_1 : problem_85_spec [11%Z; 68%Z; 34%Z; 66%Z; 44%Z; 67%Z; 77%Z; 88%Z; 99%Z; 100%Z] 322%Z.
Proof.
  unfold problem_85_spec, add_impl.
  simpl.
  unfold sum_even_at_odd_indices.
  simpl.
  (* At index 0, 11 is not added as the index is even. *)
  (* At index 1, 68 is added as it is even and the index is odd. *)
  (* At index 2, 34 is not added as the index is even. *)
  (* At index 3, 66 is added as it is even and the index is odd. *)
  (* At index 4, 44 is not added as the index is even. *)
  (* At index 5, 67 is not added as it is odd. *)
  (* At index 6, 77 is not added as the index is even. *)
  (* At index 7, 88 is added as it is even and the index is odd. *)
  (* At index 8, 99 is not added as the index is even. *)
  (* At index 9, 100 is added as it is even and the index is odd. *)
  (* The recursion ends with an empty list. *)
  reflexivity.
Qed.