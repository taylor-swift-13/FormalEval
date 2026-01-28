Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1/6"; "2/1"] -> x1=1, x2=6, n1=2, n2=1
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1 6 2 1 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res is false = true, which is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (1 * 2) mod (6 * 1) *)
    (* 1 * 2 = 2 *)
    (* 6 * 1 = 6 *)
    (* 2 mod 6 = 2 *)
    (* H_mod implies 2 = 0, which is impossible *)
    compute in H_mod.
    discriminate H_mod.
Qed.