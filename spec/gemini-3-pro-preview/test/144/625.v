Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1/10"; "10/100"] -> x1=1, x2=10, n1=10, n2=100
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1 10 10 100 false.
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
    (* Simplify algebraic expressions: (1 * 10) mod (10 * 100) *)
    (* 1 * 10 = 10 *)
    (* 10 * 100 = 1000 *)
    (* 10 mod 1000 = 10 *)
    (* H_mod becomes 10 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.