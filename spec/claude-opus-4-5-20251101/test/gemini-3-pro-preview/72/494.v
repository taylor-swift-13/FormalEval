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

Example test_will_it_fly : will_it_fly_spec [0; 1; 15; 5; 1; 3; 2; 1; 0] 8 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H.
    discriminate H.
  - (* Backward direction: (is_palindrome /\ sum <= w) -> false = true *)
    intros [Hpal Hsum].
    simpl in Hsum.
    (* The sum is 28, and 28 <= 8 is false *)
    lia.
Qed.