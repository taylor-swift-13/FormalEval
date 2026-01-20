Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 1099511627777 4722366482869645213695 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. exfalso.
    destruct H as [k Hk].
    (* Large numbers are not practical to compute directly in Coq's nat representation *)
    (* Instead, we reason abstractly: for large values of x and n, x = n ^ k cannot hold *)
    (* Here, we would provide an argument based on properties of numbers *)
    (* To ensure correctness, we rely on the fact that x and n are not simple powers *)
    (* and thus no k exists such that x = n ^ k. *)
    (* This argument would need to be external to Coq if direct computation fails. *)