Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["99999/010"; "9999/010"] -> x1=99999, x2=10, n1=9999, n2=10
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 99999 10 9999 10 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (99999 * 9999) mod (10 * 10) *)
    (* 99999 * 9999 = 999890001 *)
    (* 10 * 10 = 100 *)
    (* 999890001 mod 100 = 1 *)
    (* 1 = 0 is false *)
    compute in H_mod.
    discriminate.
Qed.