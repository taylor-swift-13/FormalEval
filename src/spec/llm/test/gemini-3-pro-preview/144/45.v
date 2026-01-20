Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["15/17"; "3/2"] -> x1=15, x2=17, n1=3, n2=2
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 15 17 3 2 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (15 * 3) mod (17 * 2) *)
    (* 15 * 3 = 45 *)
    (* 17 * 2 = 34 *)
    (* 45 mod 34 = 11 *)
    (* H_mod : 11 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.