Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition is_prime_spec (n : nat) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 ->
   ((exists i, 2 <= i < n /\ n mod i = 0) -> result = false) /\
   ((forall i, 2 <= i < n -> n mod i <> 0) -> result = true)).

Example is_prime_6_false : is_prime_spec 6 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case n <= 1 *)
    intros H.
    (* 6 <= 1 is false *)
    lia.
  - (* Case n > 1 *)
    intros H_gt.
    split.
    + (* Sub-goal: (exists divisor) -> result = false *)
      intros H_exists.
      (* result is false, so false = false holds *)
      reflexivity.
    + (* Sub-goal: (forall non-divisor) -> result = true *)
      intros H_forall.
      (* We assume result is false. To prove false = true, we must find a contradiction in the hypothesis H_forall. *)
      (* H_forall states that for all i in [2, 6), 6 mod i <> 0. *)
      (* We show this is false for i = 2. *)
      assert (H_range : 2 <= 2 < 6). { lia. }
      specialize (H_forall 2 H_range).
      (* Simplify 6 mod 2 to 0 *)
      simpl in H_forall.
      (* H_forall is now 0 <> 0, which is a contradiction *)
      contradiction.
Qed.