Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 4722366482869645213694 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    (* Here we need to show that there is no such k such that 4722366482869645213694 = 5 ^ k.
       Since 5 ^ k grows exponentially and 4722366482869645213694 is not a power of 5, 
       we conclude that no such k exists. *)
    (* This is typically a non-trivial task in Coq and would require more advanced techniques
       or automation, but for the sake of this exercise, we assume it is false. *)
    exfalso.
    (* You can use some additional lemmas or tactics to show the contradiction if needed. *)
Abort.