Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/7"; "9217/7"] -> x1=921, x2=7, n1=9217, n2=7
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 921 7 9217 7 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (921 * 9217) mod (7 * 7) *)
    (* (921 * 9217) mod 49 = 8488857 mod 49 = 48 *)
    (* 48 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.