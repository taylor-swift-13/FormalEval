Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3/2"; "3/2"] -> x1=3, x2=2, n1=3, n2=2
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3 2 3 2 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (3 * 3) mod (2 * 2) = 9 mod 4 = 1 *)
    (* H_mod implies 1 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.