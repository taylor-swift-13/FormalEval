Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["138/113"; "857/291"] -> x1=138, x2=113, n1=857, n2=291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 138 113 857 291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (138 * 857) mod (113 * 291) *)
    vm_compute in H_mod.
    (* H_mod reduces to 19617 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.