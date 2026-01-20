Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3/8"; "45553/384"] -> x1=3, x2=8, n1=45553, n2=384
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3 8 45553 384 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (3 * 45553) mod (8 * 384) *)
    vm_compute in H_mod.
    (* H_mod evaluates to 1491 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.