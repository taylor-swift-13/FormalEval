Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_prime_6 : is_prime_spec 6 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case n <= 1 *)
    intros H.
    (* 6 <= 1 is false, so the implication holds trivially *)
    lia.
  - (* Case n > 1 *)
    intros _.
    split.
    + (* Direction: result = true -> ... *)
      intros H.
      (* result is false, so false = true is a contradiction *)
      discriminate.
    + (* Direction: (forall d, ...) -> result = true *)
      intros H.
      (* We need to show that the hypothesis H implies False, 
         since result is false and false <> true.
         H states that for all d in [2, 6), d does not divide 6.
         We provide a counter-example: d = 2. *)
      specialize (H 2).
      (* Prove the bounds for d = 2 *)
      assert (H_bounds: 2 <= 2 /\ 2 < 6) by lia.
      destruct H_bounds as [H_le H_lt].
      specialize (H H_le H_lt).
      (* Compute Z.rem 6 2 *)
      simpl in H.
      (* H is now 0 <> 0, which is a contradiction *)
      contradiction.
Qed.