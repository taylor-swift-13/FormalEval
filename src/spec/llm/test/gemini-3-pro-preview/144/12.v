Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1/5"; "1/5"] -> x1=1, x2=5, n1=1, n2=5
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1 5 1 5 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (1 * 1) mod (5 * 5) *)
    (* 1 * 1 = 1 *)
    (* 5 * 5 = 25 *)
    (* 1 mod 25 = 1 *)
    (* H_mod implies 1 = 0 *)
    compute in H_mod.
    discriminate.
Qed.