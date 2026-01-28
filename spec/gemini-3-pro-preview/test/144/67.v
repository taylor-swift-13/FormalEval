Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["15/117"; "3/2"] -> x1=15, x2=117, n1=3, n2=2
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 15 117 3 2 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (15 * 3) mod (117 * 2) *)
    (* 15 * 3 = 45 *)
    (* 117 * 2 = 234 *)
    (* 45 mod 234 = 45 *)
    (* H_mod implies 45 = 0, a contradiction *)
    compute in H_mod.
    discriminate.
Qed.