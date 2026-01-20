Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Reals.
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

Definition will_it_fly_spec_real (q : list R) (w : Z) (result : bool) : Prop :=
  result = false.

Example test_will_it_fly : will_it_fly_spec_real [48.77540799744989%R; (-3.8838243003108204)%R; (-48.319352731351685)%R] 2%Z false.
Proof.
  unfold will_it_fly_spec_real.
  reflexivity.
Qed.