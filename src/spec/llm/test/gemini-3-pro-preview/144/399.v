Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2/3"; "11/9"] -> x1=2, x2=3, n1=11, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 2 3 11 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* (2 * 11) mod (3 * 9) = 22 mod 27 = 22 *)
    (* 22 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.