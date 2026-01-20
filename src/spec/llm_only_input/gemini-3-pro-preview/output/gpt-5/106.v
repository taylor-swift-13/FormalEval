Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Specification Definitions *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S k => (S k) * factorial k
  end.

Fixpoint sum_upto (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => sum_upto k + S k
  end.

Definition f_spec (n : nat) (ans : list nat) : Prop :=
  length ans = n /\
  forall i, 1 <= i <= n ->
    nth_error ans (i - 1) = Some (if Nat.even i then factorial i else sum_upto i).

(* Test Case Proof *)
Example test_case_proof : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  split.
  - (* Verify the length of the list *)
    simpl. reflexivity.
  - (* Verify the content of the list for each index i *)
    intros i [Hge Hle].
    (* We iterate through the possible values of i (1 to 5) *)
    destruct i; [ lia | ]. (* i = 0 is impossible since i >= 1 *)
    destruct i.
    + (* i = 1: Odd, expect sum_upto 1 = 1 *)
      simpl. reflexivity.
    + destruct i.
      * (* i = 2: Even, expect factorial 2 = 2 *)
        simpl. reflexivity.
      * destruct i.
        -- (* i = 3: Odd, expect sum_upto 3 = 6 *)
           simpl. reflexivity.
        -- destruct i.
           ++ (* i = 4: Even, expect factorial 4 = 24 *)
              simpl. reflexivity.
           ++ destruct i.
              ** (* i = 5: Odd, expect sum_upto 5 = 15 *)
                 simpl. reflexivity.
              ** (* i > 5 is impossible since i <= 5 *)
                 lia.
Qed.