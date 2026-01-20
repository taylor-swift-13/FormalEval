Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["98/3"; "19/13"] -> x1=98, x2=3, n1=19, n2=13
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 98 3 19 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (98 * 19) mod (3 * 13) *)
    (* (98 * 19) = 1862 *)
    (* (3 * 13) = 39 *)
    (* 1862 mod 39 = 29 *)
    (* H_mod becomes 29 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.