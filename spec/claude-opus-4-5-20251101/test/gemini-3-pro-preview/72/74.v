Require Import List.
Require Import ZArith.
Require Import Psatz. (* For lia *)
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Definition is_palindrome (l : list Z) : Prop :=
  l = rev l.

Definition will_it_fly_spec (q : list Z) (w : Z) (result : bool) : Prop :=
  result = true <-> (is_palindrome q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [0] 1 true.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Forward direction: true = true -> (is_palindrome /\ sum <= w) *)
    intros _.
    split.
    + (* Proof of is_palindrome *)
      unfold is_palindrome.
      simpl.
      reflexivity.
    + (* Proof of sum_list <= w *)
      simpl.
      lia.
  - (* Backward direction: (is_palindrome /\ sum <= w) -> true = true *)
    intros _.
    reflexivity.
Qed.