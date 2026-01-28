Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_37 : is_prime_spec 37 true.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: n <= 1 *)
    intros H.
    lia.
  - (* Case: n > 1 *)
    intros _.
    split.
    + (* Direction: result = true -> forall d ... *)
      intros _.
      intros d H_le H_lt.
      (* We must show that for any d in [2, 36], 37 % d <> 0 *)
      assert (H_cases: d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ 
                       d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18 \/ d = 19 \/ 
                       d = 20 \/ d = 21 \/ d = 22 \/ d = 23 \/ d = 24 \/ d = 25 \/ d = 26 \/ d = 27 \/ d = 28 \/ 
                       d = 29 \/ d = 30 \/ d = 31 \/ d = 32 \/ d = 33 \/ d = 34 \/ d = 35 \/ d = 36) by lia.
      repeat (destruct H_cases as [-> | H_cases]; [ vm_compute; discriminate | ]).
      (* Handle the last case d = 36 *)
      rewrite H_cases. vm_compute. discriminate.
    + (* Direction: (forall d ...) -> result = true *)
      intros _.
      reflexivity.
Qed.