Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/19"; "31683/5841"] -> x1=11, x2=19, n1=31683, n2=5841
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 19 31683 5841 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (11 * 31683) mod (19 * 5841) *)
    (* This computes to a non-zero remainder, so H_mod is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.