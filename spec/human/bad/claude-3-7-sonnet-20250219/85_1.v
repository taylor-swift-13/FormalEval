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

Example test_add_impl_88 :
  problem_85_spec [4%Z; 88%Z] 88%Z.
Proof.
  unfold problem_85_spec, add_impl.
  simpl.
  (* Inspect sum_even_at_odd_indices [4; 88] 0 *)
  (* n = 0: Nat.odd 0 = false, so the condition is false *)
  (* sum_even_at_odd_indices [88] 1 *)
  (* n = 1: Nat.odd 1 = true, and Z.even 88 = true, so 88 + 0 = 88 *)
  
  (* Show that andb (Nat.odd 0) (Z.even 4) = false *)
  assert (H0: andb (Nat.odd 0) (Z.even 4) = false).
  {
    (* Nat.odd 0 = false *)
    simpl.
    reflexivity.
  }
  rewrite H0.
  simpl.
  (* Show that andb (Nat.odd 1) (Z.even 88) = true *)
  assert (H1: andb (Nat.odd 1) (Z.even 88) = true).
  {
    simpl.
    reflexivity.
  }
  rewrite H1.
  simpl.
  reflexivity.
Qed.