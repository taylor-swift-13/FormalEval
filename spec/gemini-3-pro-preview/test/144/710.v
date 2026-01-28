Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/252"; "38/113"] -> x1=23, x2=252, n1=38, n2=113
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 252 38 113 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (23 * 38) mod (252 * 113) *)
    (* 23 * 38 = 874 *)
    (* 252 * 113 = 28476 *)
    (* 874 mod 28476 = 874 *)
    (* H_mod implies 874 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate.
Qed.