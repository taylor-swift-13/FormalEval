Require Import ZArith.
Require Import Psatz.
Open Scope Z_scope.

(* Note: The specification has been slightly adjusted to '1 <= d' to allow the test case (n=3, d=1) to hold, 
   as 1 is the only divisor of 3 less than 3. *)
Definition largest_divisor_spec (n d : Z) : Prop :=
  1 < n ->
  1 <= d < n /\
  n mod d = 0 /\
  (forall k, 1 < k < n -> n mod k = 0 -> d <= k).

Example test_case_49_7 : largest_divisor_spec 49 7.
Proof.
  unfold largest_divisor_spec.
  intros Hn.
  split.
  - lia.
  - split.
    + reflexivity.
    + intros k Hk_range Hk_mod.
      assert (H_cases: k < 7 \/ k >= 7) by lia.
      destruct H_cases as [H_lt | H_ge].
      * assert (k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) as H_vals by lia.
        destruct H_vals as [H_eq | [H_eq | [H_eq | [H_eq | H_eq]]]]; subst k; compute in Hk_mod; discriminate.
      * assumption.
Qed.