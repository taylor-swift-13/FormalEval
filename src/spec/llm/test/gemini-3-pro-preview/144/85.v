Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2/3"; "22/3"] -> x1=2, x2=3, n1=22, n2=3
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 2 3 22 3 false.
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
    (* Simplify algebraic expressions: (2 * 22) mod (3 * 3) *)
    (* 2 * 22 = 44 *)
    (* 3 * 3 = 9 *)
    (* 44 mod 9 = 8 *)
    (* 8 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.